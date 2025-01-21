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

use anyhow::{anyhow, Context};
use oak_containers_sdk::{ApplicationHandler, OakSessionContext};
use oak_hello_world_proto::oak::containers::example::enclave_application_server::{
    EnclaveApplication, EnclaveApplicationServer,
};
use oak_proto_rust::oak::session::v1::{
    PlaintextMessage, RequestWrapper, SessionRequest, SessionResponse,
};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    ServerSession, Session,
};
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

/// The struct that will hold the gRPC EnclaveApplication implementation.
struct EnclaveApplicationImplementation {
    oak_session_context: Arc<OakSessionContext>,
    // Needed while we implement noise inline.
    application_handler: Arc<Box<dyn ApplicationHandler>>,
}

impl EnclaveApplicationImplementation {
    pub fn new(
        oak_session_context: OakSessionContext,
        application_handler: Box<dyn ApplicationHandler>,
    ) -> Self {
        Self {
            oak_session_context: Arc::new(oak_session_context),
            application_handler: Arc::new(application_handler),
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
    fn decrypt_request(&mut self, session_request: &SessionRequest) -> anyhow::Result<Vec<u8>>;
    fn encrypt_response(&mut self, response: &[u8]) -> anyhow::Result<SessionResponse>;
    fn init_session(
        &mut self,
        session_request: &SessionRequest,
    ) -> anyhow::Result<Option<SessionResponse>>;
}

impl ServerSessionHelpers for ServerSession {
    fn decrypt_request(&mut self, session_request: &SessionRequest) -> anyhow::Result<Vec<u8>> {
        self.put_incoming_message(session_request).context("failed to put request")?;
        Ok(self
            .read()
            .context("failed to read decrypted message")?
            .ok_or_else(|| anyhow::anyhow!("empty plaintext response"))?
            .plaintext)
    }

    fn encrypt_response(&mut self, response: &[u8]) -> anyhow::Result<SessionResponse> {
        self.write(&PlaintextMessage { plaintext: response.to_vec() })
            .context("failed to write response")?;
        self.get_outgoing_message()
            .context("failed get get encrypted response")?
            .ok_or_else(|| anyhow::anyhow!("empty encrypted response"))
    }

    fn init_session(
        &mut self,
        session_request: &SessionRequest,
    ) -> anyhow::Result<Option<SessionResponse>> {
        self.put_incoming_message(session_request).context("failed to put request")?;
        self.get_outgoing_message().context("failed to get outgoing messge")
    }
}

#[tonic::async_trait]
impl EnclaveApplication for EnclaveApplicationImplementation {
    type LegacySessionStream = oak_containers_sdk::tonic::OakSessionStream;
    type OakSessionStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;
    type PlaintextSessionStream =
        Pin<Box<dyn Stream<Item = Result<PlaintextMessage, tonic::Status>> + Send + 'static>>;

    async fn legacy_session(
        &self,
        request: tonic::Request<tonic::Streaming<RequestWrapper>>,
    ) -> Result<tonic::Response<Self::LegacySessionStream>, tonic::Status> {
        oak_containers_sdk::tonic::oak_session(self.oak_session_context.clone(), request).await
    }

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
                    let decrypted_request = server_session.decrypt_request(&session_request)
                        .into_tonic_result("failed to decrypt request")?;
                    let plaintext_response = application_handler.handle(&decrypted_request).await
                        .into_tonic_result("application failed")?;
                    yield server_session.encrypt_response(&plaintext_response)
                        .into_tonic_result("failed to encrypt response")?;

                } else if let Some(response) = server_session.init_session(&session_request)
                        .into_tonic_result("failed process handshake")? {
                            yield response;
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
    oak_session_context: OakSessionContext,
    application_handler: Box<dyn ApplicationHandler>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(EnclaveApplicationServer::new(EnclaveApplicationImplementation::new(
            oak_session_context,
            application_handler,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
