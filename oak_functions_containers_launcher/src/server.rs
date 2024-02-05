//
// Copyright 2022 The Project Oak Authors
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
//

// TODO(#4409): this duplicates `oak_functions_launcher/src/server.rs`. Refactor these to share
// code.

use std::{net::SocketAddr, pin::Pin};

use futures::{Future, Stream, StreamExt};
use oak_functions_launcher::proto::oak::session::v1::{
    request_wrapper, response_wrapper,
    streaming_session_server::{StreamingSession, StreamingSessionServer},
    AttestationBundle, AttestationEndorsement, AttestationEvidence, EndorsedEvidence,
    GetEndorsedEvidenceResponse, GetPublicKeyResponse, InvokeResponse, RequestWrapper,
    ResponseWrapper,
};
use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence};
use tonic::{transport::Server, Request, Response, Status, Streaming};

use crate::proto::oak::functions::{
    oak_functions_client::OakFunctionsClient as GrpcOakFunctionsClient, InvokeRequest,
};

pub struct SessionProxy {
    connector_handle: GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
    evidence: Evidence,
    endorsements: Endorsements,
    encryption_public_key: Vec<u8>,
    attestation: Vec<u8>,
}

#[tonic::async_trait]
impl StreamingSession for SessionProxy {
    type StreamStream =
        Pin<Box<dyn Stream<Item = Result<ResponseWrapper, Status>> + Send + 'static>>;

    async fn stream(
        &self,
        request: Request<Streaming<RequestWrapper>>,
    ) -> Result<Response<Self::StreamStream>, tonic::Status> {
        log::info!("handling client request");
        let mut request_stream = request.into_inner();

        // TODO(#3641): Initialize all evidence fields.
        let attestation_evidence = AttestationEvidence {
            encryption_public_key: self.encryption_public_key.to_vec(),
            signing_public_key: vec![],
            attestation: self.attestation.to_vec(),
            signed_application_data: vec![],
        };
        let attestation_endorsement = AttestationEndorsement {
            tee_certificates: vec![],
            application_data: None,
        };
        #[allow(deprecated)]
        let attestation_bundle = AttestationBundle {
            attestation_evidence: Some(attestation_evidence),
            attestation_endorsement: Some(attestation_endorsement),
            evidence: Some(self.evidence.clone()),
            endorsements: Some(self.endorsements.clone()),
        };
        let endorsed_evidence = EndorsedEvidence {
            evidence: Some(self.evidence.clone()),
            endorsements: Some(self.endorsements.clone()),
        };

        let mut connector_handle = self.connector_handle.clone();

        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let request = request
                    .map_err(|err| {
                        tonic::Status::internal(format!("error reading message from request stream: {err}"))
                    })?
                    .request
                    .ok_or_else(|| tonic::Status::invalid_argument("empty request message"))?;

                let response = match request {
                    request_wrapper::Request::GetPublicKeyRequest(_) => {
                        response_wrapper::Response::GetPublicKeyResponse(GetPublicKeyResponse {
                            attestation_bundle: Some(attestation_bundle.clone()),
                        })
                    }
                    request_wrapper::Request::GetEndorsedEvidenceRequest(_) => {
                        response_wrapper::Response::GetEndorsedEvidenceResponse(GetEndorsedEvidenceResponse {
                            endorsed_evidence: Some(endorsed_evidence.clone()),
                        })
                    }
                    request_wrapper::Request::InvokeRequest(invoke_request) => {
                        #[allow(clippy::needless_update)]
                        let enclave_invoke_request = InvokeRequest {
                            encrypted_request: invoke_request.encrypted_request,
                            ..Default::default()
                        };
                        let enclave_invoke_response = connector_handle
                            .handle_user_request(enclave_invoke_request)
                            .await
                            .map_err(|err| tonic::Status::internal(format!("error handling client request: {:?}", err)))?
                            .into_inner();

                        #[allow(clippy::needless_update)]
                        response_wrapper::Response::InvokeResponse(InvokeResponse {
                            encrypted_response: enclave_invoke_response.encrypted_response,
                            ..Default::default()
                        })
                    }
                };
                yield ResponseWrapper {
                    response: Some(response),
                };
            }
        };

        Ok(Response::new(
            Box::pin(response_stream) as Self::StreamStream
        ))
    }
}

pub fn new(
    addr: SocketAddr,
    connector_handle: GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
    evidence: Evidence,
    endorsements: Endorsements,
    encryption_public_key: Vec<u8>,
    attestation: Vec<u8>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = SessionProxy {
        connector_handle,
        evidence,
        endorsements,
        encryption_public_key,
        attestation,
    };

    Server::builder()
        .add_service(StreamingSessionServer::new(server_impl))
        .serve(addr)
}
