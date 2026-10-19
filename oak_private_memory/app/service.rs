//
// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::{pin::Pin, sync::Arc};

use anyhow::anyhow;
use futures::stream::FuturesOrdered;
use log::debug;
use metrics::RequestMetricName;
use oak_private_memory_database::clock::Clock;
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    ServerSession, Session,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
};
use oak_session_tls::OakSessionTlsServerContext;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_server::{
    SealedMemoryService, SealedMemoryServiceServer,
};
use sealed_memory_rust_proto::{oak::private_memory::TlsSessionFrame, prelude::v1::*};
use tokio::{net::TcpListener, sync::mpsc};
use tokio_stream::{Stream, StreamExt, wrappers::TcpListenerStream};

use crate::{
    ApplicationConfig, IntoTonicResult,
    admission::{ActiveSessionGuard, AdmissionController, MapCountMonitor},
    context::UserSessionContext,
    db_client::SharedDbClient,
    handler::SealedMemorySessionHandler,
};

/// How often the `active_sessions` and `process_map_count` gauges are
/// refreshed in the background, so they stay current without new sessions.
/// Matches `MAP_COUNT_SAMPLE_INTERVAL`, so the refresh reads
/// `/proc/self/maps` about once per second at most.
const ADMISSION_GAUGE_REFRESH_INTERVAL: std::time::Duration = std::time::Duration::from_secs(1);

/// The gRPC service implementation.
///
/// One instance of this is created on startup. Each incoming stream creates a
/// new session handler (`OakSessionHandler` for Noise, or
/// `TlsSessionHandler` for TLS).
struct SealedMemoryServiceImplementation {
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    db_client: Arc<SharedDbClient>,
    session_config_factory: Arc<dyn Fn() -> SessionConfig + Send + Sync>,
    tls_server_context: Option<Arc<OakSessionTlsServerContext>>,
    clock: Arc<dyn Clock>,
    application_config: ApplicationConfig,
    admission: Arc<AdmissionController>,
}

impl SealedMemoryServiceImplementation {
    pub fn new(
        application_config: ApplicationConfig,
        metrics: Arc<metrics::Metrics>,
        persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
        session_config_factory: Arc<dyn Fn() -> SessionConfig + Send + Sync>,
        tls_server_context: Option<Arc<OakSessionTlsServerContext>>,
        clock: Arc<dyn Clock>,
        meminfo_reader: crate::meminfo::MemInfoReader,
    ) -> Self {
        // Panics on misconfigured thresholds to surface the error early rather
        // than silently disabling.
        let admission = Arc::new(
            AdmissionController::new(
                application_config.max_active_sessions,
                application_config.max_map_count_ratio,
                application_config.min_available_memory_ratio,
                application_config.request_min_available_memory_ratio,
                MapCountMonitor::new_for_current_process(),
                metrics.clone(),
            )
            .with_meminfo_reader(meminfo_reader),
        );

        Self {
            db_client: Arc::new(SharedDbClient::new(
                application_config.database_service_host,
                application_config.max_grpc_decode_size_bytes,
                metrics.clone(),
            )),
            metrics,
            persistence_tx,
            session_config_factory,
            tls_server_context,
            clock,
            application_config,
            admission,
        }
    }

    /// Creates a handler for a Noise session (`Invoke`, `InvokeAsync` or
    /// `StartSession`), counting the attempt under `SessionStart`.
    fn new_oak_session_handler(&self) -> tonic::Result<OakSessionHandler> {
        let handler = self.create_oak_session_handler();
        self.record_session_start(&handler);
        handler
    }

    /// Runs admission control, then creates the session's handler.
    fn create_oak_session_handler(&self) -> tonic::Result<OakSessionHandler> {
        // Admission control runs before the handshake and any Icing init.
        let session_guard = self.admission.admit()?;
        OakSessionHandler::new(
            session_guard,
            self.admission.clone(),
            &self.metrics,
            &self.persistence_tx,
            self.db_client.clone(),
            (self.session_config_factory)(),
            self.clock.clone(),
            self.application_config.max_database_size_bytes,
            self.application_config.blanket_ttl_seconds,
            self.application_config.max_memory_ttl_seconds,
            self.application_config.enable_int8_embedding,
            self.application_config.allowed_memory_sources.clone(),
        )
    }

    /// Runs admission control and rejects the TLS session if TLS is not
    /// configured, otherwise returns the session's admission guard and the TLS
    /// server context to run it with.
    fn admit_tls_session(
        &self,
    ) -> tonic::Result<(ActiveSessionGuard, &Arc<OakSessionTlsServerContext>)> {
        // Admission control runs before the TLS handshake and any Icing init.
        let session_guard = self.admission.admit()?;
        let tls_ctx = self
            .tls_server_context
            .as_ref()
            .ok_or_else(|| tonic::Status::unimplemented("TLS sessions are not configured"))?;
        Ok((session_guard, tls_ctx))
    }

    /// Counts an attempt to open a session stream under `SessionStart`, and
    /// also as a `SessionStart` failure if the stream was rejected. Neither is
    /// mirrored into `total`, which counts messages rather than streams.
    fn record_session_start<Session>(&self, session: &tonic::Result<Session>) {
        self.metrics.inc_requests(RequestMetricName::session_start());
        if let Err(status) = session {
            self.metrics.record_failure(RequestMetricName::session_start(), status.code());
        }
    }
}

/// Handles a Noise-based session (used by `Invoke` and `StartSession` RPCs).
///
/// Manages the full lifecycle: attestation + handshake init messages, then
/// encrypted application data exchange.
struct OakSessionHandler {
    metrics: Arc<metrics::Metrics>,
    server_session: ServerSession,
    application_handler: SealedMemorySessionHandler,
}

impl OakSessionHandler {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        session_guard: ActiveSessionGuard,
        admission: Arc<AdmissionController>,
        metrics: &Arc<metrics::Metrics>,
        persistence_tx: &mpsc::UnboundedSender<UserSessionContext>,
        db_client: Arc<SharedDbClient>,
        session_config: SessionConfig,
        clock: Arc<dyn Clock>,
        max_database_size_bytes: usize,
        blanket_ttl_seconds: i64,
        max_memory_ttl_seconds: i64,
        enable_int8_embedding: bool,
        allowed_memory_sources: Vec<String>,
    ) -> tonic::Result<Self> {
        let server_session = ServerSession::create(session_config)
            .into_failed_precondition("failed to initialize oak session")?;
        Ok(Self {
            metrics: metrics.clone(),
            server_session,
            application_handler: SealedMemorySessionHandler::new(
                metrics.clone(),
                persistence_tx.clone(),
                db_client,
                clock,
                max_database_size_bytes,
                blanket_ttl_seconds,
                max_memory_ttl_seconds,
                enable_int8_embedding,
                allowed_memory_sources,
            )
            .with_session_guard(session_guard)
            .with_admission(admission),
        })
    }

    pub async fn handle_start_session_request(
        &mut self,
        request: tonic::Result<SealedMemorySessionRequest>,
    ) -> tonic::Result<Option<SessionResponse>> {
        // A stream receive error is not a request, so only received messages
        // are counted, as in `run_concurrent_dispatch`.
        let request = request?;
        self.metrics.inc_requests(RequestMetricName::total());
        let session_request = match request
            .session_request
            .into_invalid_argument("request is missing session request")
        {
            Ok(session_request) => session_request,
            Err(e) => {
                self.metrics.inc_requests(RequestMetricName::empty_request());
                self.metrics.record_failure(RequestMetricName::empty_request(), e.code());
                return Err(e);
            }
        };
        self.handle_session_request(session_request).await
    }

    pub async fn handle_invoke_request(
        &mut self,
        session_request: tonic::Result<SessionRequest>,
    ) -> tonic::Result<Option<SessionResponse>> {
        // A stream receive error is not a request, so only received messages
        // are counted, as in `run_concurrent_dispatch`.
        let session_request = session_request?;
        self.metrics.inc_requests(RequestMetricName::total());
        self.handle_session_request(session_request).await
    }

    async fn handle_session_request(
        &mut self,
        session_request: SessionRequest,
    ) -> tonic::Result<Option<SessionResponse>> {
        if self.server_session.is_open() {
            self.handle_app_request(session_request).await
        } else {
            self.handle_init_request(session_request).await
        }
    }

    async fn handle_init_request(
        &mut self,
        session_request: SessionRequest,
    ) -> tonic::Result<Option<SessionResponse>> {
        self.metrics.inc_requests(RequestMetricName::handshake());
        if let Err(e) = self
            .server_session
            .handle_init_message(session_request)
            .into_internal_error("failed to handle init request")
        {
            self.metrics.record_failure(RequestMetricName::handshake(), e.code());
            return Err(e);
        }

        if !self.server_session.is_open() {
            match self
                .server_session
                .next_init_message()
                .into_internal_error("failed to get next init message")
            {
                Ok(r) => Ok(Some(r)),
                Err(e) => {
                    // TODO: b/571198870 - not covered by a metric test:
                    // `next_init_message` only fails on an internal Noise state
                    // error after `handle_init_message` accepted the client's
                    // message, which a client can't trigger.
                    self.metrics.record_failure(RequestMetricName::handshake(), e.code());
                    Err(e)
                }
            }
        } else {
            Ok(None)
        }
    }

    async fn handle_app_request(
        &mut self,
        session_request: SessionRequest,
    ) -> tonic::Result<Option<SessionResponse>> {
        let decrypted_request = match self.server_session.decrypt(session_request) {
            Ok(req) => req,
            Err(e) => {
                self.metrics.inc_requests(RequestMetricName::decryption_failure());
                self.metrics.record_failure(
                    RequestMetricName::decryption_failure(),
                    tonic::Code::InvalidArgument,
                );
                return Err(tonic::Status::invalid_argument(format!(
                    "failed to decrypt request: {e}"
                )));
            }
        };

        // On error, the handler has already recorded the failure under its
        // request type.
        let plaintext_response = self.application_handler.handle(&decrypted_request).await?;
        match self
            .server_session
            .encrypt(plaintext_response)
            .into_internal_error("failed to encrypt response")
        {
            Ok(response) => Ok(Some(response)),
            Err(e) => {
                // TODO: b/571198870 - not covered by a metric test:
                // encryption only fails on an internal Noise state error,
                // which a client can't trigger. The request type is unknown
                // here, so the failure is recorded under `total` only. If the
                // response is an error response, the handler already counted
                // it in `total`, so this counts it twice.
                self.metrics.record_failure(RequestMetricName::total(), e.code());
                Err(e)
            }
        }
    }
}

/// Handles a TLS-based session (used by `StartTlsSession` RPC).
///
///
/// The TLS handshake is completed before this handler processes any application
/// data.
struct TlsSessionHandler {
    metrics: Arc<metrics::Metrics>,
    session: oak_session_tls::OakSessionTls,
    application_handler: SealedMemorySessionHandler,
}

impl TlsSessionHandler {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        session_guard: ActiveSessionGuard,
        admission: Arc<AdmissionController>,
        metrics: &Arc<metrics::Metrics>,
        persistence_tx: &mpsc::UnboundedSender<UserSessionContext>,
        db_client: Arc<SharedDbClient>,
        tls_session: oak_session_tls::OakSessionTls,
        clock: Arc<dyn Clock>,
        max_database_size_bytes: usize,
        blanket_ttl_seconds: i64,
        max_memory_ttl_seconds: i64,
        enable_int8_embedding: bool,
        allowed_memory_sources: Vec<String>,
    ) -> Self {
        Self {
            metrics: metrics.clone(),
            session: tls_session,
            application_handler: SealedMemorySessionHandler::new(
                metrics.clone(),
                persistence_tx.clone(),
                db_client,
                clock,
                max_database_size_bytes,
                blanket_ttl_seconds,
                max_memory_ttl_seconds,
                enable_int8_embedding,
                allowed_memory_sources,
            )
            .with_session_guard(session_guard)
            .with_admission(admission),
        }
    }
}

#[tonic::async_trait]
impl SealedMemoryService for SealedMemoryServiceImplementation {
    type InvokeStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;
    type InvokeAsyncStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;
    type StartSessionStream = Pin<
        Box<dyn Stream<Item = Result<SealedMemorySessionResponse, tonic::Status>> + Send + 'static>,
    >;
    type StartTlsSessionStream =
        Pin<Box<dyn Stream<Item = Result<TlsSessionFrame, tonic::Status>> + Send + 'static>>;

    async fn invoke(
        &self,
        request: tonic::Request<tonic::Streaming<SessionRequest>>,
    ) -> Result<tonic::Response<Self::InvokeStream>, tonic::Status> {
        let mut oak_session_handler = self.new_oak_session_handler()?;

        let mut request_stream = request.into_inner();
        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let response = oak_session_handler.handle_invoke_request(request).await?;
                if let Some(response) = response { yield response; }
            }
            debug!("Enclave Stream finished");
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::InvokeStream))
    }

    async fn invoke_async(
        &self,
        request: tonic::Request<tonic::Streaming<SessionRequest>>,
    ) -> Result<tonic::Response<Self::InvokeAsyncStream>, tonic::Status> {
        let mut oak_session_handler = self.new_oak_session_handler()?;

        let mut request_stream = request.into_inner();
        let (tx, rx) = tokio::sync::mpsc::channel(32);

        tokio::spawn(async move {
            // Phase 1: Handshake — process init messages sequentially until the
            // session is open.
            while !oak_session_handler.server_session.is_open() {
                match request_stream.next().await {
                    Some(request) => {
                        match oak_session_handler.handle_invoke_request(request).await {
                            Ok(Some(response)) => {
                                if tx.send(Ok(response)).await.is_err() {
                                    return;
                                }
                            }
                            Ok(None) => {}
                            Err(e) => {
                                let _ = tx.send(Err(e)).await;
                                return;
                            }
                        }
                    }
                    None => return,
                }
            }

            // Phase 2: Concurrent dispatch of application requests.
            let OakSessionHandler { metrics, server_session, application_handler } =
                oak_session_handler;
            let mut crypto = NoiseSessionCrypto { server_session, metrics: metrics.clone() };
            run_concurrent_dispatch(
                &mut request_stream,
                &tx,
                &metrics,
                Arc::new(application_handler),
                &mut crypto,
            )
            .await;
            debug!("Enclave Async Stream finished");
        });

        let response_stream = tokio_stream::wrappers::ReceiverStream::new(rx);
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::InvokeAsyncStream))
    }

    async fn start_session(
        &self,
        request: tonic::Request<tonic::Streaming<SealedMemorySessionRequest>>,
    ) -> Result<tonic::Response<Self::StartSessionStream>, tonic::Status> {
        let mut oak_session_handler = self.new_oak_session_handler()?;

        let mut request_stream = request.into_inner();
        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let session_response = oak_session_handler.handle_start_session_request(request).await?;
                if session_response.is_some() {
                    yield SealedMemorySessionResponse { session_response }
                }
            }
            debug!("Enclave Stream finished");
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StartSessionStream))
    }

    async fn start_tls_session(
        &self,
        request: tonic::Request<tonic::Streaming<TlsSessionFrame>>,
    ) -> Result<tonic::Response<Self::StartTlsSessionStream>, tonic::Status> {
        let admitted = self.admit_tls_session();
        self.record_session_start(&admitted);
        let (session_guard, tls_ctx) = admitted?;

        let admission = self.admission.clone();
        let metrics = self.metrics.clone();
        let persistence_tx = self.persistence_tx.clone();
        let db_client = self.db_client.clone();
        let clock = self.clock.clone();
        let max_database_size_bytes = self.application_config.max_database_size_bytes;
        let blanket_ttl_seconds = self.application_config.blanket_ttl_seconds;
        let max_memory_ttl_seconds = self.application_config.max_memory_ttl_seconds;
        let enable_int8_embedding = self.application_config.enable_int8_embedding;
        let allowed_memory_sources = self.application_config.allowed_memory_sources.clone();

        let request_stream = Arc::new(tokio::sync::Mutex::new(request.into_inner()));
        let (tx, rx) = tokio::sync::mpsc::channel(32);
        let tls_ctx = tls_ctx.clone();

        tokio::spawn(async move {
            // The whole handshake counts as one request, in the total too, as
            // its failure is recorded in the total.
            metrics.inc_requests(RequestMetricName::total());
            metrics.inc_requests(RequestMetricName::handshake());

            let handshake_result = tls_ctx
                .new_initialized_session(
                    |frame| {
                        let tx = tx.clone();
                        async move {
                            tx.send(Ok(TlsSessionFrame { tls_frame: frame }))
                                .await
                                .map_err(|_| anyhow!("client disconnected during handshake"))
                        }
                    },
                    {
                        let rs = request_stream.clone();
                        move || {
                            let rs = rs.clone();
                            async move {
                                match rs.lock().await.next().await {
                                    Some(Ok(in_frame)) => Ok(Some(in_frame.tls_frame)),
                                    Some(Err(e)) => Err(anyhow!("receive failed: {e}")),
                                    None => Ok(None),
                                }
                            }
                        }
                    },
                )
                .await;

            let (tls_session, _initial_data) = match handshake_result {
                Ok(res) => res,
                Err(e) => {
                    log::error!("TLS handshake failed: {}", e);
                    metrics.inc_tls_handshake_failures();
                    metrics.record_failure(RequestMetricName::handshake(), tonic::Code::Internal);
                    let _ = tx
                        .send(Err(tonic::Status::internal(format!("handshake failed: {}", e))))
                        .await;
                    return;
                }
            };

            let tls_handler = TlsSessionHandler::new(
                session_guard,
                admission,
                &metrics,
                &persistence_tx,
                db_client,
                tls_session,
                clock,
                max_database_size_bytes,
                blanket_ttl_seconds,
                max_memory_ttl_seconds,
                enable_int8_embedding,
                allowed_memory_sources,
            );
            debug!("TLS handshake completed");

            let mut stream =
                Arc::into_inner(request_stream).expect("exclusive ownership").into_inner();

            // Phase 2: Concurrent dispatch of application requests.
            let TlsSessionHandler { metrics: handler_metrics, session, application_handler } =
                tls_handler;
            let mut crypto = TlsSessionCrypto {
                session,
                metrics: handler_metrics.clone(),
                outer_metrics: metrics.clone(),
            };
            run_concurrent_dispatch(
                &mut stream,
                &tx,
                &handler_metrics,
                Arc::new(application_handler),
                &mut crypto,
            )
            .await;
            debug!("TLS Stream finished");
        });

        let response_stream = tokio_stream::wrappers::ReceiverStream::new(rx);
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StartTlsSessionStream))
    }
}
/// Abstracts over the crypto operations for a session (Noise or TLS).
///
/// This allows the [`run_concurrent_dispatch`] function to work with both
/// session types without code duplication.
trait SessionCrypto {
    /// The wire-format request type read from the gRPC stream.
    type Request;
    /// The wire-format response type sent back on the gRPC stream.
    type Response: Send + 'static;

    /// Decrypts an incoming request into plaintext bytes.
    ///
    /// Returns `Ok(None)` to silently skip the request (e.g. empty TLS frames),
    /// `Ok(Some(bytes))` to dispatch to the application handler, or `Err` to
    /// abort the stream.
    fn decrypt(&mut self, request: Self::Request) -> tonic::Result<Option<Vec<u8>>>;

    /// Encrypts a plaintext response into the wire-format response type.
    fn encrypt(&mut self, plaintext: Vec<u8>) -> tonic::Result<Self::Response>;

    /// Called when the stream yields an error instead of a request.
    fn on_receive_error(&self, error: tonic::Status);
}

/// [`SessionCrypto`] implementation for Noise-based sessions (Invoke RPC).
struct NoiseSessionCrypto {
    server_session: ServerSession,
    metrics: Arc<metrics::Metrics>,
}

impl SessionCrypto for NoiseSessionCrypto {
    type Request = SessionRequest;
    type Response = SessionResponse;

    fn decrypt(&mut self, request: SessionRequest) -> tonic::Result<Option<Vec<u8>>> {
        match self.server_session.decrypt(request) {
            Ok(decrypted) => Ok(Some(decrypted)),
            Err(e) => {
                self.metrics.inc_requests(RequestMetricName::decryption_failure());
                self.metrics.record_failure(
                    RequestMetricName::decryption_failure(),
                    tonic::Code::InvalidArgument,
                );
                Err(tonic::Status::invalid_argument(format!("failed to decrypt request: {e}")))
            }
        }
    }

    fn encrypt(&mut self, plaintext: Vec<u8>) -> tonic::Result<SessionResponse> {
        self.server_session.encrypt(plaintext).into_internal_error("failed to encrypt response")
    }

    fn on_receive_error(&self, e: tonic::Status) {
        log::error!("error receiving request: {e}");
    }
}

/// [`SessionCrypto`] implementation for TLS-based sessions (StartTlsSession
/// RPC).
struct TlsSessionCrypto {
    session: oak_session_tls::OakSessionTls,
    metrics: Arc<metrics::Metrics>,
    outer_metrics: Arc<metrics::Metrics>,
}

impl SessionCrypto for TlsSessionCrypto {
    type Request = TlsSessionFrame;
    type Response = TlsSessionFrame;

    fn decrypt(&mut self, request: TlsSessionFrame) -> tonic::Result<Option<Vec<u8>>> {
        match self.session.decrypt(&request.tls_frame).map_err(|e| {
            self.metrics.inc_requests(RequestMetricName::decryption_failure());
            self.metrics.record_failure(
                RequestMetricName::decryption_failure(),
                tonic::Code::InvalidArgument,
            );
            tonic::Status::invalid_argument(format!("failed to decrypt TLS request: {e}"))
        }) {
            Ok(decrypted) if decrypted.is_empty() => {
                self.metrics.inc_requests(RequestMetricName::empty_tls_frame());
                Ok(None)
            }
            Ok(decrypted) => Ok(Some(decrypted)),
            Err(e) => Err(e),
        }
    }

    fn encrypt(&mut self, plaintext: Vec<u8>) -> tonic::Result<TlsSessionFrame> {
        let response_bytes = self
            .session
            .encrypt(&plaintext)
            .map_err(|e| tonic::Status::internal(format!("failed to encrypt TLS response: {e}")))?;
        Ok(TlsSessionFrame { tls_frame: response_bytes })
    }

    fn on_receive_error(&self, e: tonic::Status) {
        log::error!("error receiving TLS data: {e}");
        self.outer_metrics.inc_tls_receive_failures();
    }
}

/// Returns a handler task's result. Handler errors are returned unchanged, as
/// the handler has already recorded them. A panicked task is recorded as a
/// failure under `total`, because its request type is unknown.
fn handler_task_result(
    join_result: Result<tonic::Result<Vec<u8>>, tokio::task::JoinError>,
    metrics: &metrics::Metrics,
) -> tonic::Result<Vec<u8>> {
    join_result.unwrap_or_else(|join_error| {
        metrics.record_failure(RequestMetricName::total(), tonic::Code::Internal);
        Err(tonic::Status::internal(format!("handler task panicked: {join_error}")))
    })
}

/// Runs the concurrent dispatch loop shared by both Noise and TLS handlers.
///
/// Reads requests from `stream`, decrypts them via `crypto`, dispatches the
/// application handler concurrently via `tokio::spawn`, then encrypts
/// responses and sends them through `tx` — all while preserving the original
/// request order via `FuturesOrdered`.
async fn run_concurrent_dispatch<S, C>(
    stream: &mut S,
    tx: &tokio::sync::mpsc::Sender<Result<C::Response, tonic::Status>>,
    metrics: &Arc<metrics::Metrics>,
    application_handler: Arc<SealedMemorySessionHandler>,
    crypto: &mut C,
) where
    S: StreamExt<Item = Result<C::Request, tonic::Status>> + Unpin,
    C: SessionCrypto,
{
    let mut in_flight: FuturesOrdered<tokio::task::JoinHandle<tonic::Result<Vec<u8>>>> =
        FuturesOrdered::new();
    let mut stream_done = false;

    // Sends an error to the client. Used before breaking out of the loop.
    macro_rules! send_err_and_break {
        ($status:expr) => {{
            let _ = tx.send(Err($status)).await;
            break;
        }};
    }

    loop {
        tokio::select! {
            // A spawned handler task completed — encrypt and forward the response.
            Some(join_result) = in_flight.next(), if !in_flight.is_empty() => {
                let plaintext = match handler_task_result(join_result, metrics) {
                    Ok(bytes) => bytes,
                    // Error already recorded, so no need to record here.
                    Err(e) => send_err_and_break!(e),
                };
                match crypto.encrypt(plaintext) {
                    Ok(response) => {
                        if tx.send(Ok(response)).await.is_err() {
                            break;
                        }
                    }
                    Err(e) => {
                        metrics.record_failure(RequestMetricName::total(), e.code());
                        send_err_and_break!(e);
                    }
                }
            }

            // A new request arrived — decrypt and spawn a handler task.
            request_res = stream.next(), if !stream_done => {
                match request_res {
                    Some(Ok(request)) => {
                        metrics.inc_requests(RequestMetricName::total());
                        match crypto.decrypt(request) {
                            Ok(Some(decrypted)) => {
                                let handler = application_handler.clone();
                                in_flight.push_back(tokio::spawn(
                                    async move { handler.handle(&decrypted).await },
                                ));
                            }
                            Ok(None) => {} // empty frame, skip
                            Err(e) => send_err_and_break!(e),
                        }
                    }
                    Some(Err(e)) => {
                        crypto.on_receive_error(e);
                        stream_done = true;
                    }
                    None => stream_done = true,
                }
            }

            else => break,
        }
    }
}

/// Creates the gRPC server with both Noise and TLS session support.
///
/// The `tls_server_context` is optional: if `None`, TLS sessions will return
/// `UNIMPLEMENTED` when clients attempt to connect via `StartTlsSession`.
pub async fn create(
    listener: TcpListener,
    application_config: ApplicationConfig,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    session_config_factory: Arc<dyn Fn() -> SessionConfig + Send + Sync>,
    tls_server_context: Option<Arc<OakSessionTlsServerContext>>,
    clock: Arc<dyn Clock>,
) -> Result<(), anyhow::Error> {
    create_with_meminfo_reader(
        listener,
        application_config,
        metrics,
        persistence_tx,
        session_config_factory,
        tls_server_context,
        clock,
        crate::meminfo::system_meminfo_reader(),
    )
    .await
}

/// Like [`create`], but uses `meminfo_reader` to sample available memory (used
/// in integration tests to simulate memory pressure changes after sessions are
/// already open).
#[allow(clippy::too_many_arguments)]
pub async fn create_with_meminfo_reader(
    listener: TcpListener,
    application_config: ApplicationConfig,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    session_config_factory: Arc<dyn Fn() -> SessionConfig + Send + Sync>,
    tls_server_context: Option<Arc<OakSessionTlsServerContext>>,
    clock: Arc<dyn Clock>,
    meminfo_reader: crate::meminfo::MemInfoReader,
) -> Result<(), anyhow::Error> {
    let max_grpc_decode_size_bytes = application_config.max_grpc_decode_size_bytes;
    let service = SealedMemoryServiceImplementation::new(
        application_config,
        metrics,
        persistence_tx,
        session_config_factory,
        tls_server_context,
        clock,
        meminfo_reader,
    );

    // Keep the admission gauges fresh even when no new sessions arrive. The
    // task holds only a weak reference so it ends with the service.
    let admission = Arc::downgrade(&service.admission);
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(ADMISSION_GAUGE_REFRESH_INTERVAL);
        loop {
            interval.tick().await;
            let Some(admission) = admission.upgrade() else { break };
            admission.refresh_gauges();
        }
    });

    tonic::transport::Server::builder()
        .add_service(
            SealedMemoryServiceServer::new(service)
                .max_decoding_message_size(max_grpc_decode_size_bytes),
        )
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeMap,
        net::{IpAddr, Ipv4Addr, SocketAddr},
    };

    use metrics_testing::{Attrs, attrs};
    use oak_private_memory_database::{
        clock::SystemClock,
        database::{MAX_DATABASE_SIZE, MAX_GRPC_DECODE_SIZE},
    };
    use prost::Message;

    use super::*;
    use crate::{MAX_MEMORY_TTL_SECONDS, METADATA_BLANKET_TTL_SECONDS};

    type TestMetrics = metrics_testing::TestMetrics<metrics::Metrics>;

    fn test_metrics() -> TestMetrics {
        TestMetrics::new(metrics::Metrics::new)
    }

    /// The `rpc_count` series for `request_type`.
    fn request_series(request_type: &str) -> Attrs {
        attrs(&[("request_type", request_type)])
    }

    /// The `rpc_failure_count` series for `request_type` and `status_code`.
    fn failure_series(request_type: &str, status_code: &str) -> Attrs {
        attrs(&[("request_type", request_type), ("status_code", status_code)])
    }

    /// A [`SessionCrypto`] that passes plaintext through unchanged, and can be
    /// told to fail encryption.
    struct FakeSessionCrypto {
        fail_encrypt: bool,
    }

    impl SessionCrypto for FakeSessionCrypto {
        type Request = Vec<u8>;
        type Response = Vec<u8>;

        fn decrypt(&mut self, request: Vec<u8>) -> tonic::Result<Option<Vec<u8>>> {
            Ok(Some(request))
        }

        fn encrypt(&mut self, plaintext: Vec<u8>) -> tonic::Result<Vec<u8>> {
            if self.fail_encrypt {
                Err(tonic::Status::internal("injected encryption failure"))
            } else {
                Ok(plaintext)
            }
        }

        fn on_receive_error(&self, _error: tonic::Status) {}
    }

    /// Returns a handler whose database is unreachable, for requests that are
    /// handled without it.
    fn handler_without_database(metrics: Arc<metrics::Metrics>) -> SealedMemorySessionHandler {
        let unreachable = SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 1);
        let db_client =
            Arc::new(SharedDbClient::new(unreachable, MAX_GRPC_DECODE_SIZE, metrics.clone()));
        let (persistence_tx, _) = mpsc::unbounded_channel();
        SealedMemorySessionHandler::new(
            metrics,
            persistence_tx,
            db_client,
            Arc::new(SystemClock),
            MAX_DATABASE_SIZE,
            METADATA_BLANKET_TTL_SECONDS,
            MAX_MEMORY_TTL_SECONDS,
            false,
            vec![],
        )
    }

    /// Runs [`run_concurrent_dispatch`] on `requests`, and returns the status
    /// code of each response it sends back.
    async fn dispatch(
        metrics: &Arc<metrics::Metrics>,
        handler: SealedMemorySessionHandler,
        crypto: &mut FakeSessionCrypto,
        requests: Vec<Vec<u8>>,
    ) -> Vec<tonic::Code> {
        let mut stream = tokio_stream::iter(requests.into_iter().map(Ok::<_, tonic::Status>));
        // Large enough to hold every response a test produces.
        let (response_sender, mut responses) = mpsc::channel(32);
        run_concurrent_dispatch(&mut stream, &response_sender, metrics, Arc::new(handler), crypto)
            .await;
        drop(response_sender);
        let mut codes = vec![];
        while let Some(response) = responses.recv().await {
            codes.push(response.map_or_else(|status| status.code(), |_| tonic::Code::Ok));
        }
        codes
    }

    /// A panicked handler task fails its request. The request type is unknown
    /// by then, so the failure is recorded under the total only.
    #[tokio::test]
    async fn handler_task_panic_is_counted_in_total_only() {
        let harness = test_metrics();
        let before = harness.collect();
        let join_error =
            tokio::spawn(async { panic!("injected handler panic") }).await.unwrap_err();

        let result = handler_task_result(Err(join_error), &harness.metrics);

        assert_eq!(result.unwrap_err().code(), tonic::Code::Internal);
        assert_eq!(
            harness.collect().counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([(failure_series("total", "INTERNAL"), 1)])
        );
    }

    /// A response that can't be encrypted fails its request. The request type
    /// is unknown by then, so the failure is recorded under the total only.
    #[tokio::test(flavor = "multi_thread")]
    async fn dispatch_counts_encryption_failure_in_total_only() {
        let harness = test_metrics();
        let before = harness.collect();
        // Key sync without a key succeeds, with an unsuccessful status, before
        // it would reach the database.
        let request = SealedMemoryRequest {
            request: Some(
                sealed_memory_request::Request::KeySyncRequest(KeySyncRequest::default()),
            ),
            request_id: 7,
        };

        let codes = dispatch(
            &harness.metrics,
            handler_without_database(harness.metrics.clone()),
            &mut FakeSessionCrypto { fail_encrypt: true },
            vec![request.encode_to_vec()],
        )
        .await;

        assert_eq!(codes, [tonic::Code::Internal]);
        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_count"),
            BTreeMap::from([(request_series("total"), 1), (request_series("KeySyncRequest"), 1)])
        );
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([(failure_series("total", "INTERNAL"), 1)])
        );
    }

    /// A request that the handler fails is recorded by the handler, and not
    /// recorded again by the dispatch loop.
    #[tokio::test(flavor = "multi_thread")]
    async fn dispatch_does_not_count_handler_errors_again() {
        let harness = test_metrics();
        let before = harness.collect();

        let codes = dispatch(
            &harness.metrics,
            handler_without_database(harness.metrics.clone()),
            &mut FakeSessionCrypto { fail_encrypt: false },
            vec![vec![0xFF; 4]],
        )
        .await;

        assert_eq!(codes, [tonic::Code::Internal]);
        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_count"),
            BTreeMap::from([
                (request_series("total"), 1),
                (request_series("DeserializationFailure"), 1),
            ])
        );
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([
                (failure_series("DeserializationFailure", "INTERNAL"), 1),
                (failure_series("total", "INTERNAL"), 1),
            ])
        );
    }

    /// Returns a Noise session handler before its handshake, whose database
    /// is unreachable.
    fn oak_session_handler_without_database(metrics: &Arc<metrics::Metrics>) -> OakSessionHandler {
        let session_config = SessionConfig::builder(
            oak_session::attestation::AttestationType::Unattested,
            oak_session::handshake::HandshakeType::NoiseNN,
        )
        .build();
        OakSessionHandler {
            metrics: metrics.clone(),
            server_session: ServerSession::create(session_config).unwrap(),
            application_handler: handler_without_database(metrics.clone()),
        }
    }

    /// A stream receive error ends an `Invoke` or `StartSession` stream, but
    /// it isn't a request, so it isn't counted. A received message is.
    #[tokio::test(flavor = "multi_thread")]
    async fn session_streams_count_received_messages_only() {
        let harness = test_metrics();
        let mut handler = oak_session_handler_without_database(&harness.metrics);
        let before = harness.collect();

        let invoke =
            handler.handle_invoke_request(Err(tonic::Status::cancelled("receive failed"))).await;
        assert_eq!(invoke.unwrap_err().code(), tonic::Code::Cancelled);
        let start_session = handler
            .handle_start_session_request(Err(tonic::Status::cancelled("receive failed")))
            .await;
        assert_eq!(start_session.unwrap_err().code(), tonic::Code::Cancelled);
        let snapshot = harness.collect();
        assert_eq!(snapshot.counter_increments(&before, "rpc_count"), BTreeMap::new());
        assert_eq!(snapshot.counter_increments(&before, "rpc_failure_count"), BTreeMap::new());

        let empty =
            handler.handle_start_session_request(Ok(SealedMemorySessionRequest::default())).await;
        assert_eq!(empty.unwrap_err().code(), tonic::Code::InvalidArgument);
        assert_eq!(
            harness.collect().counter_increments(&before, "rpc_count"),
            BTreeMap::from([(request_series("total"), 1), (request_series("EmptyRequest"), 1)])
        );
    }
}
