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

use std::{net::SocketAddr, pin::Pin};

use futures::{Future, Stream, StreamExt};
use oak_grpc::oak::session::v1::streaming_session_server::{
    StreamingSession, StreamingSessionServer,
};
use oak_proto_rust::oak::{
    attestation::v1::{Endorsements, Evidence},
    session::v1::{
        EndorsedEvidence, GetEndorsedEvidenceResponse, InvokeResponse, RequestWrapper,
        ResponseWrapper, request_wrapper, response_wrapper,
    },
};
use tonic::{Request, Response, Status, Streaming, transport::Server};

use crate::channel::ConnectorHandle;

pub struct SessionProxy {
    connector_handle: ConnectorHandle,
    evidence: Evidence,
    endorsements: Endorsements,
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

        let endorsed_evidence = EndorsedEvidence {
            evidence: Some(self.evidence.clone()),
            endorsements: Some(self.endorsements.clone()),
        };
        let connector_handle = self.connector_handle.clone();

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
                            endorsed_evidence: Some(endorsed_evidence.clone()),
                        })
                    }
                    request_wrapper::Request::InvokeRequest(invoke_request) => {
                        #[allow(clippy::needless_update)]
                        let enclave_invoke_request = oak_proto_rust::oak::functions::InvokeRequest {
                            encrypted_request: invoke_request.encrypted_request,
                            ..Default::default()
                        };
                        let mut enclave_client =
                            oak_micro_rpc::oak::functions::OakFunctionsAsyncClient::new(connector_handle.clone());
                        let enclave_invoke_response = enclave_client
                            .handle_user_request(&enclave_invoke_request)
                            .await
                            .flatten()
                            .map_err(|err| {
                                tonic::Status::internal(format!("error handling client request: {:?}", err))
                            })?;
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

        Ok(Response::new(Box::pin(response_stream) as Self::StreamStream))
    }
}

pub fn new(
    addr: SocketAddr,
    connector_handle: ConnectorHandle,
    evidence: Evidence,
    endorsements: Endorsements,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = SessionProxy { connector_handle, evidence, endorsements };

    Server::builder().add_service(StreamingSessionServer::new(server_impl)).serve(addr)
}
