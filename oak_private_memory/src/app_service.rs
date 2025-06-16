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

use anyhow::{anyhow, Context};
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_sdk_server_v1::{ApplicationHandler, OakApplicationContext};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    ServerSession, Session,
};
use opentelemetry::KeyValue;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_server::{
    SealedMemoryService, SealedMemoryServiceServer,
};
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

use crate::{app::SealedMemoryHandler, debug, metrics};

/// The struct that will hold the gRPC EnclaveApplication implementation.
struct SealedMemoryServiceImplementation {
    #[allow(dead_code)]
    oak_application_context: Arc<OakApplicationContext>,
    // Needed while we implement noise inline.
    application_handler: crate::app::SealedMemoryHandler,
    #[allow(dead_code)]
    metrics: Arc<metrics::Metrics>,
}

impl SealedMemoryServiceImplementation {
    pub fn new(
        oak_application_context: OakApplicationContext,
        application_handler: SealedMemoryHandler,
        metrics: Arc<metrics::Metrics>,
    ) -> Self {
        Self {
            oak_application_context: Arc::new(oak_application_context),
            application_handler,
            metrics,
        }
    }

    async fn handle_session_request(
        application_handler: &SealedMemoryHandler,
        server_session: &mut ServerSession,
        session_request: SessionRequest,
    ) -> Result<Option<SessionResponse>, tonic::Status> {
        if server_session.is_open() {
            let decrypted_request = server_session
                .decrypt_request(session_request)
                .into_tonic_result("failed to decrypt request")?;
            let plaintext_response = application_handler.handle(&decrypted_request).await;
            if plaintext_response.is_err() {
                application_handler
                    .metrics
                    .rpc_failure_count
                    .add(1, &[KeyValue::new("request_type", "total")]);
            }
            let plaintext_response = plaintext_response.into_tonic_result("application failed")?;
            Ok(Some(
                server_session
                    .encrypt_response(&plaintext_response)
                    .into_tonic_result("failed to encrypt response")?,
            ))
        } else {
            application_handler
                .metrics
                .rpc_count
                .add(1, &[KeyValue::new("request_type", "Handshake")]);
            let response = server_session
                .init_session(session_request)
                .into_tonic_result("failed process handshake");
            if response.is_err() {
                application_handler
                    .metrics
                    .rpc_failure_count
                    .add(1, &[KeyValue::new("request_type", "Handshake")]);
            }
            response
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

trait ServerSessionHelpers {
    fn decrypt_request(&mut self, session_request: SessionRequest) -> anyhow::Result<Vec<u8>>;
    fn encrypt_response(&mut self, response: &[u8]) -> anyhow::Result<SessionResponse>;
    fn init_session(
        &mut self,
        session_request: SessionRequest,
    ) -> anyhow::Result<Option<SessionResponse>>;
}

impl ServerSessionHelpers for ServerSession {
    fn decrypt_request(&mut self, session_request: SessionRequest) -> anyhow::Result<Vec<u8>> {
        self.put_incoming_message(session_request).context("failed to put request")?;
        Ok(self
            .read()
            .context("failed to read decrypted message")?
            .ok_or_else(|| anyhow::anyhow!("empty plaintext response"))?
            .plaintext)
    }

    fn encrypt_response(&mut self, response: &[u8]) -> anyhow::Result<SessionResponse> {
        self.write(PlaintextMessage { plaintext: response.to_vec() })
            .context("failed to write response")?;
        self.get_outgoing_message()
            .context("failed get get encrypted response")?
            .ok_or_else(|| anyhow::anyhow!("empty encrypted response"))
    }

    fn init_session(
        &mut self,
        session_request: SessionRequest,
    ) -> anyhow::Result<Option<SessionResponse>> {
        self.put_incoming_message(session_request).context("failed to put request")?;
        self.get_outgoing_message().context("failed to get outgoing messge")
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
        let mut server_session = ServerSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .map_err(|e| tonic::Status::internal(format!("could not create server session: {e:?}")))?;

        let application_handler = self.application_handler.clone();

        let mut request_stream = request.into_inner();
        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                application_handler.metrics.rpc_count.add(1, &[KeyValue::new("request_type", "total")]);
                debug!("Receive request!!");
                let session_request = request?;

                if let Some(response) = Self::handle_session_request(&application_handler,
                    &mut server_session,
                    session_request,
                ).await? {
                    yield response;
                }
            }
            debug!("Enclave Stream finished");
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::InvokeStream))
    }

    async fn start_session(
        &self,
        request: tonic::Request<tonic::Streaming<SealedMemorySessionRequest>>,
    ) -> Result<tonic::Response<Self::StartSessionStream>, tonic::Status> {
        let mut server_session = ServerSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .map_err(|e| tonic::Status::internal(format!("could not create server session: {e:?}")))?;

        let application_handler = self.application_handler.clone();

        let mut request_stream = request.into_inner();
        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                application_handler.metrics.rpc_count.add(1, &[KeyValue::new("request_type", "total")]);
                let session_request = request?.session_request.ok_or_else(|| tonic::Status::internal("failed to get session request"))?;

                if let Some(response) = Self::handle_session_request(&application_handler,
                    &mut server_session,
                    session_request,
                ).await? {
                    yield SealedMemorySessionResponse {
                        session_response: Some(response),
                    };
                }
            }
            debug!("Enclave Stream finished");
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StartSessionStream))
    }
}

pub async fn create(
    listener: TcpListener,
    oak_session_context: OakApplicationContext,
    application_handler: SealedMemoryHandler,
    metrics: Arc<metrics::Metrics>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(
            SealedMemoryServiceServer::new(SealedMemoryServiceImplementation::new(
                oak_session_context,
                application_handler,
                metrics,
            ))
            .max_decoding_message_size(20 * 1024 * 1024), /* 20MB */
        )
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
