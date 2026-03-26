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
use session::{EncryptedSession, TlsEncryptedSession};
use tokio::{net::TcpListener, sync::mpsc};
use tokio_stream::{Stream, StreamExt, wrappers::TcpListenerStream};

use crate::{
    ApplicationConfig, IntoTonicResult, context::UserSessionContext, db_client::SharedDbClient,
    handler::SealedMemorySessionHandler,
};

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
}

impl SealedMemoryServiceImplementation {
    pub fn new(
        application_config: ApplicationConfig,
        metrics: Arc<metrics::Metrics>,
        persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
        session_config_factory: Arc<dyn Fn() -> SessionConfig + Send + Sync>,
        tls_server_context: Option<Arc<OakSessionTlsServerContext>>,
        clock: Arc<dyn Clock>,
    ) -> Self {
        Self {
            metrics,
            persistence_tx,
            db_client: Arc::new(SharedDbClient::new(application_config.database_service_host)),
            session_config_factory,
            tls_server_context,
            clock,
        }
    }

    fn new_oak_session_handler(&self) -> tonic::Result<OakSessionHandler> {
        OakSessionHandler::new(
            &self.metrics,
            &self.persistence_tx,
            self.db_client.clone(),
            (self.session_config_factory)(),
            self.clock.clone(),
        )
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
    pub fn new(
        metrics: &Arc<metrics::Metrics>,
        persistence_tx: &mpsc::UnboundedSender<UserSessionContext>,
        db_client: Arc<SharedDbClient>,
        session_config: SessionConfig,
        clock: Arc<dyn Clock>,
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
            ),
        })
    }

    pub async fn handle_start_session_request(
        &mut self,
        request: tonic::Result<SealedMemorySessionRequest>,
    ) -> tonic::Result<Option<SessionResponse>> {
        self.metrics.inc_requests(RequestMetricName::total());
        let session_request =
            request?.session_request.into_invalid_argument("request is missing session request")?;
        self.handle_session_request(session_request).await
    }

    pub async fn handle_invoke_request(
        &mut self,
        session_request: tonic::Result<SessionRequest>,
    ) -> tonic::Result<Option<SessionResponse>> {
        self.metrics.inc_requests(RequestMetricName::total());
        self.handle_session_request(session_request?).await
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
        self.server_session
            .handle_init_message(session_request)
            .into_internal_error("failed to handle init request")?;

        if !self.server_session.is_open() {
            match self
                .server_session
                .next_init_message()
                .into_internal_error("failed to get next init message")
            {
                Ok(r) => Ok(Some(r)),
                Err(e) => {
                    self.metrics.inc_failures(RequestMetricName::handshake());
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
        let decrypted_request = self
            .server_session
            .decrypt(session_request)
            .into_invalid_argument("failed to decrypt request")?;

        match self.application_handler.handle(&decrypted_request).await {
            Err(e) => {
                self.metrics.inc_failures(RequestMetricName::total());
                Err(e)
            }
            Ok(plaintext_response) => Ok(Some(
                self.server_session
                    .encrypt(plaintext_response)
                    .into_internal_error("failed to encrypt response")?,
            )),
        }
    }
}

/// Handles a TLS-based session (used by `StartTlsSession` RPC).
///
/// The TLS handshake is completed before this handler processes any application
/// data. All encrypt/decrypt goes through the [`EncryptedSession`] trait.
struct TlsSessionHandler {
    metrics: Arc<metrics::Metrics>,
    session: TlsEncryptedSession,
    application_handler: SealedMemorySessionHandler,
}

impl TlsSessionHandler {
    pub fn new(
        metrics: &Arc<metrics::Metrics>,
        persistence_tx: &mpsc::UnboundedSender<UserSessionContext>,
        db_client: Arc<SharedDbClient>,
        tls_session: oak_session_tls::OakSessionTls,
        clock: Arc<dyn Clock>,
    ) -> Self {
        Self {
            metrics: metrics.clone(),
            session: TlsEncryptedSession::new(tls_session),
            application_handler: SealedMemorySessionHandler::new(
                metrics.clone(),
                persistence_tx.clone(),
                db_client,
                clock,
            ),
        }
    }

    /// Handles a TLS application request (raw encrypted bytes in, raw encrypted
    /// bytes out).
    pub async fn handle_app_request(&mut self, encrypted_request: &[u8]) -> tonic::Result<Vec<u8>> {
        self.metrics.inc_requests(RequestMetricName::total());

        let decrypted_request = self
            .session
            .decrypt(encrypted_request)
            .into_invalid_argument("failed to decrypt TLS request")?;

        if decrypted_request.is_empty() {
            // This can happen if the TLS frame only contained handshake data
            // (e.g., tickets, key updates) but no application data. We should
            // gracefully return empty bytes instead of failing to deserialize.
            return Ok(Vec::new());
        }

        match self.application_handler.handle(&decrypted_request).await {
            Err(e) => {
                self.metrics.inc_failures(RequestMetricName::total());
                Err(e)
            }
            Ok(plaintext_response) => self
                .session
                .encrypt(&plaintext_response)
                .into_internal_error("failed to encrypt TLS response"),
        }
    }
}

#[tonic::async_trait]
impl SealedMemoryService for SealedMemoryServiceImplementation {
    type InvokeStream =
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
        let tls_ctx = self
            .tls_server_context
            .as_ref()
            .ok_or_else(|| tonic::Status::unimplemented("TLS sessions are not configured"))?;

        let metrics = self.metrics.clone();
        let persistence_tx = self.persistence_tx.clone();
        let db_client = self.db_client.clone();
        let clock = self.clock.clone();

        let request_stream = Arc::new(tokio::sync::Mutex::new(request.into_inner()));
        let (tx, rx) = tokio::sync::mpsc::channel(32);
        let tls_ctx = tls_ctx.clone();

        tokio::spawn(async move {
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

            let (tls_session, mut _initial_data) = match handshake_result {
                Ok(res) => res,
                Err(e) => {
                    log::error!("TLS handshake failed: {}", e);
                    let _ = tx
                        .send(Err(tonic::Status::internal(format!("handshake failed: {}", e))))
                        .await;
                    return;
                }
            };

            let mut tls_handler =
                TlsSessionHandler::new(&metrics, &persistence_tx, db_client, tls_session, clock);
            debug!("TLS handshake completed");

            let mut stream =
                Arc::into_inner(request_stream).expect("exclusive ownership").into_inner();

            // Phase 2: Application data exchange.
            while let Some(request_res) = stream.next().await {
                let request = match request_res {
                    Ok(req) => req,
                    Err(e) => {
                        log::error!("Error receiving TLS data: {}", e);
                        break;
                    }
                };

                match tls_handler.handle_app_request(&request.tls_frame).await {
                    Ok(response_bytes) => {
                        if !response_bytes.is_empty()
                            && tx
                                .send(Ok(TlsSessionFrame { tls_frame: response_bytes }))
                                .await
                                .is_err()
                        {
                            break;
                        }
                    }
                    Err(e) => {
                        let _ = tx.send(Err(e)).await;
                        break;
                    }
                }
            }
            debug!("TLS Stream finished");
        });

        let response_stream = tokio_stream::wrappers::ReceiverStream::new(rx);
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StartTlsSessionStream))
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
    tonic::transport::Server::builder()
        .add_service(
            SealedMemoryServiceServer::new(SealedMemoryServiceImplementation::new(
                application_config,
                metrics,
                persistence_tx,
                session_config_factory,
                tls_server_context,
                clock,
            ))
            .max_decoding_message_size(crate::db_client::MAX_DECODE_SIZE),
        )
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
