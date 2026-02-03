//
// Copyright 2023 The Project Oak Authors
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

/// App service shows an example of the boilerplate needed to implement the
/// Oak-related machinery for session message stream handling.
///
/// Oak doesn't provide full service implementation conveniences in the SDK,
/// since typically, Oak-enabled methods will be part of a larger service that
/// may need to be configured in specific ways.
use std::{pin::Pin, sync::Arc};

use anyhow::anyhow;
use oak_hello_world_proto::oak::containers::example::enclave_application_server::{
    EnclaveApplication, EnclaveApplicationServer,
};
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{
    ServerSession, Session,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
};
use tokio::net::TcpListener;
use tokio_stream::{Stream, StreamExt, wrappers::TcpListenerStream};

use crate::app::HelloWorldApplicationHandler;

/// The struct that will hold the gRPC EnclaveApplication implementation.
struct EnclaveApplicationImplementation {
    // Needed while we implement noise inline.
    application_handler: Arc<HelloWorldApplicationHandler>,
}

impl EnclaveApplicationImplementation {
    pub fn new(application_handler: HelloWorldApplicationHandler) -> Self {
        Self { application_handler: Arc::new(application_handler) }
    }
}

trait IntoTonicResult<T> {
    #[allow(clippy::result_large_err)]
    fn into_tonic_result(self, context: &str) -> tonic::Result<T>;
}

impl<T> IntoTonicResult<T> for anyhow::Result<T> {
    fn into_tonic_result(self, context: &str) -> tonic::Result<T> {
        self.map_err(|e| tonic::Status::internal(format!("{context}: {e:?}")))
    }
}

#[tonic::async_trait]
impl EnclaveApplication for EnclaveApplicationImplementation {
    type OakSessionStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;
    type PlaintextSessionStream =
        Pin<Box<dyn Stream<Item = Result<PlaintextMessage, tonic::Status>> + Send + 'static>>;

    async fn oak_session(
        &self,
        request: tonic::Request<tonic::Streaming<SessionRequest>>,
    ) -> Result<tonic::Response<Self::OakSessionStream>, tonic::Status> {
        let mut server_session = ServerSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .map_err(|e| tonic::Status::internal(format!("could not create server session: {e:?}")))?;

        let application_handler = self.application_handler.clone();

        let mut request_stream = request.into_inner();
        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let session_request = request?;
                if server_session.is_open() {
                    let decrypted_request = server_session.decrypt(session_request)
                        .into_tonic_result("failed to decrypt request")?;
                    let plaintext_response = application_handler.handle(&decrypted_request).await
                        .into_tonic_result("application failed")?;
                    yield server_session.encrypt(plaintext_response)
                        .into_tonic_result("failed to encrypt response")?;

                } else {
                    server_session.handle_init_message(session_request).into_tonic_result("failed to process init request")?;
                    if !server_session.is_open() {
                        yield server_session.next_init_message().into_tonic_result("failed to get init response")?;
                    }
                }
            }
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::OakSessionStream))
    }

    async fn plaintext_session(
        &self,
        request: tonic::Request<tonic::Streaming<PlaintextMessage>>,
    ) -> Result<tonic::Response<Self::PlaintextSessionStream>, tonic::Status> {
        let mut request_stream = request.into_inner();
        let application_handler = self.application_handler.clone();

        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let plaintext_message = request?;
                    yield PlaintextMessage {
                        plaintext: application_handler
                            .handle(&plaintext_message.plaintext)
                            .await
                            .into_tonic_result("application failed")?
                    };
            }
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::PlaintextSessionStream))
    }
}

pub async fn create(
    listener: TcpListener,
    application_handler: HelloWorldApplicationHandler,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(EnclaveApplicationServer::new(EnclaveApplicationImplementation::new(
            application_handler,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
