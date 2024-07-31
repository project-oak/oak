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

use std::{pin::Pin, sync::Arc};

use anyhow::anyhow;
use oak_containers_sdk::InstanceEncryptionKeyHandle;
use oak_crypto::encryptor::ServerEncryptor;
use oak_hello_world_proto::oak::containers::example::trusted_application_server::{
    TrustedApplication, TrustedApplicationServer,
};
use oak_proto_rust::oak::{
    crypto::v1::{EncryptedRequest, EncryptedResponse},
    session::v1::{
        request_wrapper, response_wrapper, EndorsedEvidence, GetEndorsedEvidenceResponse,
        InvokeRequest, InvokeResponse, RequestWrapper, ResponseWrapper,
    },
};
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

// Things that need to be available to every incoming streaming session.
struct SessionContext {
    application_config: Vec<u8>,
    encryption_key_handle: InstanceEncryptionKeyHandle,
    endorsed_evidence: EndorsedEvidence,
}

struct TrustedApplicationImplementation {
    session_context: Arc<SessionContext>,
}

impl TrustedApplicationImplementation {
    pub fn new(
        application_config: Vec<u8>,
        encryption_key_handle: InstanceEncryptionKeyHandle,
        endorsed_evidence: EndorsedEvidence,
    ) -> Self {
        Self {
            session_context: Arc::new(SessionContext {
                application_config,
                encryption_key_handle,
                endorsed_evidence,
            }),
        }
    }
}

impl SessionContext {
    fn handle_hello(&self, request_bytes: &[u8]) -> String {
        let name = String::from_utf8_lossy(request_bytes);
        format!(
            "Hello from the trusted side, {}! Btw, the Trusted App has a config with a length of {} bytes.",
            name,
            self.application_config.len()
        )
    }

    async fn handle_request(
        &self,
        encrypted_request: Option<EncryptedRequest>,
    ) -> tonic::Result<EncryptedResponse> {
        let encrypted_request = encrypted_request
            .ok_or(tonic::Status::internal("encrypted request wasn't provided"))?;

        // Associated data is ignored.
        let (server_encryptor, name_bytes, _) =
            ServerEncryptor::decrypt_async(&encrypted_request, &self.encryption_key_handle)
                .await
                .map_err(|error| {
                tonic::Status::internal(format!("couldn't decrypt request: {:?}", error))
            })?;

        let response = self.handle_hello(&name_bytes);

        server_encryptor.encrypt(response.as_bytes(), EMPTY_ASSOCIATED_DATA).map_err(|error| {
            tonic::Status::internal(format!("couldn't encrypt response: {:?}", error))
        })
    }
}

#[tonic::async_trait]
impl TrustedApplication for TrustedApplicationImplementation {
    type SessionStream =
        Pin<Box<dyn Stream<Item = Result<ResponseWrapper, tonic::Status>> + Send + 'static>>;

    async fn session(
        &self,
        request: tonic::Request<tonic::Streaming<RequestWrapper>>,
    ) -> Result<tonic::Response<Self::SessionStream>, tonic::Status> {
        let mut request_stream = request.into_inner();

        let session_context = self.session_context.clone();

        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let request = request
                    .map_err(|err| {
                        tonic::Status::internal(format!("error reading message from request stream: {err}"))
                    })?
                    .request
                    .ok_or_else(|| tonic::Status::invalid_argument("empty request message"))?;

                let response = match request {
                    request_wrapper::Request::GetEndorsedEvidenceRequest(_) => {
                        response_wrapper::Response::GetEndorsedEvidenceResponse(GetEndorsedEvidenceResponse {
                            endorsed_evidence: Some(session_context.endorsed_evidence.clone()),
                        })
                    }
                    request_wrapper::Request::InvokeRequest(InvokeRequest { encrypted_request }) => {
                        let encrypted_response = session_context.handle_request(encrypted_request)
                            .await
                            .map_err(|err| tonic::Status::internal(format!("hello failed: {err:?}")))?;
                        response_wrapper::Response::InvokeResponse(
                            InvokeResponse { encrypted_response: Some(encrypted_response) }
                        )
                    }
                };
                yield ResponseWrapper {
                    response: Some(response),
                };
            }
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::SessionStream))
    }
}

pub async fn create(
    listener: TcpListener,
    application_config: Vec<u8>,
    encryption_key_handle: InstanceEncryptionKeyHandle,
    endorsed_evidence: EndorsedEvidence,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(TrustedApplicationServer::new(TrustedApplicationImplementation::new(
            application_config,
            encryption_key_handle,
            endorsed_evidence,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
