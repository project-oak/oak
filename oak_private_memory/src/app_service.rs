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
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    ServerSession, Session,
};
use opentelemetry::KeyValue;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_server::{
    SealedMemoryService, SealedMemoryServiceServer,
};
use sealed_memory_rust_proto::prelude::v1::*;
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

use crate::{app::SealedMemoryHandler, log::debug, metrics};

/// The struct that will hold the gRPC EnclaveApplication implementation.
struct SealedMemoryServiceImplementation {
    // Needed while we implement noise inline.
    application_handler: crate::app::SealedMemoryHandler,
    #[allow(dead_code)]
    metrics: Arc<metrics::Metrics>,
}

impl SealedMemoryServiceImplementation {
    pub fn new(application_handler: SealedMemoryHandler, metrics: Arc<metrics::Metrics>) -> Self {
        Self { application_handler, metrics }
    }

    async fn handle_session_request(
        application_handler: &SealedMemoryHandler,
        server_session: &mut ServerSession,
        session_request: SessionRequest,
    ) -> tonic::Result<Option<SessionResponse>> {
        if server_session.is_open() {
            Self::handle_app_request(application_handler, server_session, session_request).await
        } else {
            Self::handle_init_request(application_handler, server_session, session_request).await
        }
    }

    async fn handle_init_request(
        application_handler: &SealedMemoryHandler,
        server_session: &mut ServerSession,
        session_request: SessionRequest,
    ) -> tonic::Result<Option<SessionResponse>> {
        application_handler.metrics.rpc_count.add(1, &[KeyValue::new("request_type", "Handshake")]);
        server_session
            .handle_init_message(session_request)
            .into_tonic_result("failed to handle init request")?;

        // The server may optionally need to send an init response.
        if !server_session.is_open() {
            match server_session
                .next_init_message()
                .into_tonic_result("failed to get next init message")
            {
                Ok(r) => Ok(Some(r)),
                Err(e) => {
                    application_handler
                        .metrics
                        .rpc_failure_count
                        .add(1, &[KeyValue::new("request_type", "Handshake")]);
                    Err(e)
                }
            }
        } else {
            Ok(None)
        }
    }

    async fn handle_app_request(
        application_handler: &SealedMemoryHandler,
        server_session: &mut ServerSession,
        session_request: SessionRequest,
    ) -> tonic::Result<Option<SessionResponse>> {
        let decrypted_request = server_session
            .decrypt(session_request)
            .into_tonic_result("failed to decrypt request")?;

        match application_handler.handle(&decrypted_request).await {
            Err(e) => {
                application_handler
                    .metrics
                    .rpc_failure_count
                    .add(1, &[KeyValue::new("request_type", "total")]);
                Err(e).into_tonic_result("failed to handle message")
            }
            Ok(plaintext_response) => Ok(Some(
                server_session
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
                let response =
                    Self::handle_session_request(&application_handler, &mut server_session, session_request)
                    .await?;
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
                let session_response =
                    Self::handle_session_request(&application_handler, &mut server_session, session_request)
                    .await?;
                yield SealedMemorySessionResponse { session_response }
            }
            debug!("Enclave Stream finished");
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StartSessionStream))
    }
}

pub async fn create(
    listener: TcpListener,
    application_handler: SealedMemoryHandler,
    metrics: Arc<metrics::Metrics>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(
            SealedMemoryServiceServer::new(SealedMemoryServiceImplementation::new(
                application_handler,
                metrics,
            ))
            .max_decoding_message_size(20 * 1024 * 1024), /* 20MB */
        )
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
