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
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    ServerSession, Session,
};
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_server::{
    SealedMemoryService, SealedMemoryServiceServer,
};
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::{net::TcpListener, sync::mpsc};
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

use crate::{
    context::UserSessionContext, db_client::SharedDbClient, handler::SealedMemorySessionHandler,
    ApplicationConfig,
};

// The struct that holds the service implementation.
// One instance of this is created on startup.
struct SealedMemoryServiceImplementation {
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    db_client: Arc<SharedDbClient>,
}

impl SealedMemoryServiceImplementation {
    pub fn new(
        application_config: ApplicationConfig,
        metrics: Arc<metrics::Metrics>,
        persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
    ) -> Self {
        Self {
            metrics,
            persistence_tx,
            db_client: Arc::new(SharedDbClient::new(application_config.database_service_host)),
        }
    }

    fn new_oak_session_handler(&self) -> anyhow::Result<OakSessionHandler> {
        OakSessionHandler::new(&self.metrics, &self.persistence_tx, self.db_client.clone())
    }
}

// The handler for oak session messages, that handles both init messages and app
// messages.
//
// A new instances of this is created on each new stream creation.
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
    ) -> anyhow::Result<Self> {
        Ok(Self {
            metrics: metrics.clone(),
            server_session: ServerSession::create(
                SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
            )?,
            application_handler: SealedMemorySessionHandler::new(
                metrics.clone(),
                persistence_tx.clone(),
                db_client,
            ),
        })
    }

    pub async fn handle_start_session_request(
        &mut self,
        request: tonic::Result<SealedMemorySessionRequest>,
    ) -> tonic::Result<Option<SessionResponse>> {
        self.metrics.inc_requests(RequestMetricName::total());
        let session_request = request?
            .session_request
            .ok_or_else(|| tonic::Status::internal("failed to get session request"))?;
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
            .into_tonic_result("failed to handle init request")?;

        // The server may optionally need to send an init response.
        if !self.server_session.is_open() {
            match self
                .server_session
                .next_init_message()
                .into_tonic_result("failed to get next init message")
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
            .into_tonic_result("failed to decrypt request")?;

        match self.application_handler.handle(&decrypted_request).await {
            Err(e) => {
                self.metrics.inc_failures(RequestMetricName::total());
                Err(e).into_tonic_result("failed to handle message")
            }
            Ok(plaintext_response) => Ok(Some(
                self.server_session
                    .encrypt(plaintext_response)
                    .into_tonic_result("failed to encrypt response")?,
            )),
        }
    }
}

trait IntoTonicResult<T> {
    fn into_tonic_result(self, context: &str) -> tonic::Result<T>;
}

impl<T> IntoTonicResult<T> for anyhow::Result<T> {
    fn into_tonic_result(self, context: &str) -> tonic::Result<T> {
        self.map_err(|e| tonic::Status::internal(format!("{context}: {e:?}")))
    }
}

#[tonic::async_trait]
impl SealedMemoryService for SealedMemoryServiceImplementation {
    type InvokeStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;
    type StartSessionStream = Pin<
        Box<dyn Stream<Item = Result<SealedMemorySessionResponse, tonic::Status>> + Send + 'static>,
    >;

    async fn invoke(
        &self,
        request: tonic::Request<tonic::Streaming<SessionRequest>>,
    ) -> Result<tonic::Response<Self::InvokeStream>, tonic::Status> {
        let mut oak_session_handler =
            self.new_oak_session_handler().into_tonic_result("Failed to create session handler")?;

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
        let mut oak_session_handler =
            self.new_oak_session_handler().into_tonic_result("Failed to create session handler")?;

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
}

pub async fn create(
    listener: TcpListener,
    application_config: ApplicationConfig,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(
            SealedMemoryServiceServer::new(SealedMemoryServiceImplementation::new(
                application_config,
                metrics,
                persistence_tx,
            ))
            .max_decoding_message_size(crate::db_client::MAX_DECODE_SIZE),
        )
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
