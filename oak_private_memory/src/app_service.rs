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
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_server::{
    SealedMemoryService, SealedMemoryServiceServer,
};
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

use crate::{app::SealedMemoryHandler, debug};

/// The struct that will hold the gRPC EnclaveApplication implementation.
struct SealedMemoryServiceImplementation {
    #[allow(dead_code)]
    oak_application_context: Arc<OakApplicationContext>,
    // Needed while we implement noise inline.
    application_handler: crate::app::SealedMemoryHandler,
}

impl SealedMemoryServiceImplementation {
    pub fn new(
        oak_application_context: OakApplicationContext,
        application_handler: SealedMemoryHandler,
    ) -> Self {
        Self { oak_application_context: Arc::new(oak_application_context), application_handler }
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
                debug!("Receive request!!");
                let session_request = request?;
                if server_session.is_open() {
                    let decrypted_request = server_session.decrypt_request(session_request)
                        .into_tonic_result("failed to decrypt request")?;
                    let plaintext_response = application_handler.handle(&decrypted_request).await
                        .into_tonic_result("application failed")?;
                    yield server_session.encrypt_response(&plaintext_response)
                        .into_tonic_result("failed to encrypt response")?;

                } else if let Some(response) = server_session.init_session(session_request)
                        .into_tonic_result("failed process handshake")? {
                            yield response;
                }
            }
            debug!("Enclave Stream finished");
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::InvokeStream))
    }
}

pub async fn create(
    listener: TcpListener,
    oak_session_context: OakApplicationContext,
    application_handler: SealedMemoryHandler,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(SealedMemoryServiceServer::new(SealedMemoryServiceImplementation::new(
            oak_session_context,
            application_handler,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
