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

use crate::{channel::ConnectorHandle, schema};
use futures::{Future, Stream, StreamExt};
use oak_remote_attestation_noninteractive::proto::{
    request_wrapper, response_wrapper, streaming_session_server::StreamingSessionServer,
    InvokeResponse, RequestWrapper, ResponseWrapper,
};
use std::{net::SocketAddr, pin::Pin};
use tonic::{transport::Server, Request, Response, Status, Streaming};

pub struct SessionProxy {
    connector_handle: ConnectorHandle,
    // TODO(#3442): Return cached key and attestation when clients ask for it.
    _signing_public_key: Vec<u8>,
    _attestation: Vec<u8>,
}

#[tonic::async_trait]
impl oak_remote_attestation_noninteractive::proto::streaming_session_server::StreamingSession
    for SessionProxy
{
    type StreamStream = Pin<Box<dyn Stream<Item = Result<ResponseWrapper, Status>> + Send>>;

    async fn stream(
        &self,
        request: Request<Streaming<RequestWrapper>>,
    ) -> Result<Response<Self::StreamStream>, tonic::Status> {
        log::info!("handling client request");
        let mut request_stream = request.into_inner();
        let request = request_stream
            .next()
            .await
            .ok_or_else(|| tonic::Status::invalid_argument("empty request stream"))?
            .map_err(|err| {
                tonic::Status::internal(format!("error reading message from request stream: {err}"))
            })?;
        let Some(request_wrapper::Request::InvokeRequest(invoke_request)) = request.request else {
            return Err(tonic::Status::invalid_argument("request wrapper must have invoke_request field set"));
        };
        let encoded_request = schema::InvokeRequest {
            body: invoke_request.encrypted_body,
        };

        let mut client = schema::OakFunctionsAsyncClient::new(self.connector_handle.clone());

        let response = client
            .invoke(&encoded_request)
            .await
            .flatten()
            .map_err(|err| {
                tonic::Status::internal(format!("error handling client request: {:?}", err))
            })?;

        Ok(Response::new(Box::pin(futures::stream::iter(vec![Ok(
            ResponseWrapper {
                response: Some(response_wrapper::Response::InvokeResponse(InvokeResponse {
                    encrypted_body: response.body,
                })),
            },
        )]))))
    }
}

pub fn new(
    addr: SocketAddr,
    connector_handle: ConnectorHandle,
    signing_public_key: Vec<u8>,
    attestation: Vec<u8>,
) -> impl Future<Output = Result<(), tonic::transport::Error>> {
    let server_impl = SessionProxy {
        connector_handle,
        _signing_public_key: signing_public_key,
        _attestation: attestation,
    };

    Server::builder()
        .add_service(StreamingSessionServer::new(server_impl))
        .serve(addr)
}
