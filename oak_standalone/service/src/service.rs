//
// Copyright 2024 The Project Oak Authors
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
use futures::{Stream, StreamExt};
use oak_crypto::{encryption_key::EncryptionKey, encryptor::ServerEncryptor};
use oak_grpc::oak::session::v1::streaming_session_server::{
    StreamingSession, StreamingSessionServer,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        endorsements, ApplicationKeys, Endorsements, Evidence, OakStandaloneEndorsements,
        RootLayerEvidence, TeePlatform,
    },
    session::v1::{
        request_wrapper, response_wrapper, EndorsedEvidence, GetEndorsedEvidenceResponse,
        InvokeResponse, RequestWrapper, ResponseWrapper,
    },
};
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

/// A simple request/response adapter between a client application and the Oak
/// Standalone facade.
///
/// Note: This is very similar to the [micro_rpc::Transport] trait. That type is
/// a great candidate for implementing an Adapter. But since other approaches
/// might be possible too, we keep the adapter type separate for now.
pub trait Adapter: Send + Sync {
    /// Invoke the client request for the provided serialized request string.
    ///
    /// The client should return a serialized response message that the Oak
    /// Standalone facade will encrypt and return to the client.
    fn invoke(&self, serialized_request: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// The structure that will implement the Oak Streaming Session crypto service
/// on behalf of a client's application. Right now, it just sets up the crypto
/// channel, but doesn't interact with any application yet.
struct OakStandaloneServiceImpl {
    /// The private encryption key that will be used by the server to encrypt
    /// response.
    private_encryption_key: Arc<EncryptionKey>,

    /// The EndorsedEvidence to be sent to clients, containing the public key
    /// needed to establish an encryption channel.
    ///
    /// The Oak Client protocol expected to receive an EndorsedEvidence
    /// structure. Normally, the client would use the attestation
    /// verification library to ensure that the provided endorsed evidence
    /// is valid, and then extract the key from that; the application key
    /// would have been derive from the entire DICE chain.
    /// For now, we just hack the raw public key bytes into the field, and
    /// use a special [StandaloneAttestationVerifier] that just pull the public
    /// key out.
    ///
    /// Why start with such a seemingly overcomplicated approach? The idea is
    /// that we'd like to stick to the established Oak protocol, so that:
    /// * We might add some sort of attestation/transparent release support.
    /// * It's easier to transition later to a full Oak stack implementation.
    endorsed_evidence: Arc<EndorsedEvidence>,

    adapter: Arc<dyn Adapter>,
}

impl OakStandaloneServiceImpl {
    /// Create a new instance of the server using the provided keypair.
    fn new(
        private_encryption_key: EncryptionKey,
        public_key: Vec<u8>,
        adapter: Arc<dyn Adapter>,
    ) -> Self {
        Self {
            private_encryption_key: Arc::new(private_encryption_key),

            endorsed_evidence: Arc::new(EndorsedEvidence {
                evidence: Some(Evidence {
                    // TODO: b/347970899 - Create something here that will be compatible with the
                    // verification framework.
                    root_layer: Some(RootLayerEvidence {
                        platform: TeePlatform::None.into(),
                        eca_public_key: vec![],
                        remote_attestation_report: vec![],
                    }),
                    layers: vec![],
                    application_keys: Some(ApplicationKeys {
                        // TODO: b/347970899 - Store the public key in the format expected by
                        // the attestation verification framework.
                        encryption_public_key_certificate: public_key,
                        group_encryption_public_key_certificate: vec![],
                        signing_public_key_certificate: vec![],
                        group_signing_public_key_certificate: vec![],
                    }),
                }),
                endorsements: Some(Endorsements {
                    r#type: Some(endorsements::Type::Standalone(OakStandaloneEndorsements {})),
                }),
            }),
            adapter,
        }
    }
}

#[tonic::async_trait]
impl StreamingSession for OakStandaloneServiceImpl {
    type StreamStream =
        Pin<Box<dyn Stream<Item = Result<ResponseWrapper, tonic::Status>> + Send + 'static>>;

    async fn stream(
        &self,
        request: tonic::Request<tonic::Streaming<RequestWrapper>>,
    ) -> Result<tonic::Response<Self::StreamStream>, tonic::Status> {
        let mut request_stream = request.into_inner();

        let private_key = self.private_encryption_key.clone();
        let endorsed_evidence = self.endorsed_evidence.clone();
        let adapter = self.adapter.clone();

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
                            endorsed_evidence: Some((*endorsed_evidence).clone()),
                        })
                    }
                    request_wrapper::Request::InvokeRequest(encrypted_request) => {
                        let (server_encryptor, decrypted_request, _request_associated_data) =
                            ServerEncryptor::decrypt(&encrypted_request.encrypted_request.unwrap(), &*private_key)
                            .expect("server couldn't decrypt request");

                        let response = adapter.invoke(&decrypted_request)
                            .map_err(|err| tonic::Status::internal(format!("invoke failed: {err:?}")))?;

                        let encrypted_response = server_encryptor.encrypt(&response, b"")
                            .map_err(|err| tonic::Status::internal(format!("encrypt failed: {err:?}")))?;
                        response_wrapper::Response::InvokeResponse(InvokeResponse {
                            encrypted_response: Some(encrypted_response)
                        })
                    }
                };
                yield ResponseWrapper {
                    response: Some(response),
                };
            }
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::StreamStream))
    }
}

pub async fn create(
    listener: TcpListener,
    private_encryption_key: EncryptionKey,
    public_key: Vec<u8>,
    adapter: Arc<dyn Adapter>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(StreamingSessionServer::new(OakStandaloneServiceImpl::new(
            private_encryption_key,
            public_key,
            adapter,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
