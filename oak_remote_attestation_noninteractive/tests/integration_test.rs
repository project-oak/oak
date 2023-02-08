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
//

use anyhow::Context;
use futures::{Stream, StreamExt};
use oak_remote_attestation_noninteractive::proto::{
    request_wrapper, response_wrapper,
    streaming_session_client::StreamingSessionClient,
    streaming_session_server::{StreamingSession, StreamingSessionServer},
    AttestationEvidence, GetPublicKeyRequest, GetPublicKeyResponse, RequestWrapper,
    ResponseWrapper,
};
use std::pin::Pin;
use tonic::{
    transport::{Channel, Server},
    Request, Response, Status, Streaming,
};

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_get_public_key() {
    let port = 54321;

    let handle = tokio::spawn(async move {
        let _ = start_server(port).await;
    });

    let result = run_client(port).await;
    assert!(result.is_ok());

    handle.abort();
}

async fn start_server(port: u16) -> Result<(), tonic::transport::Error> {
    let address = format!("[::1]:{port}").parse().unwrap();
    let server = Server::builder()
        .add_service(StreamingSessionServer::new(TestEvidenceProviderServer {}))
        .serve(address);

    server.await
}

async fn run_client(port: u16) -> anyhow::Result<()> {
    // TODO(#3641): Replace with a call to the OakClient, once it supports sending
    // GetPublicKeyRequest.
    let channel = Channel::from_shared(format!("http://[::1]:{port}"))
        .context("couldn't create gRPC channel")?
        .connect()
        .await?;
    let mut inner = StreamingSessionClient::new(channel);

    let mut response_stream = inner
        .stream(futures_util::stream::iter(vec![RequestWrapper {
            request: Some(request_wrapper::Request::GetPublicKeyRequest(
                GetPublicKeyRequest {},
            )),
        }]))
        .await
        .context("couldn't send message")?
        .into_inner();

    // Read the next (and only) message from the response stream.
    let response_wrapper = response_stream
        .message()
        .await
        .context("gRPC server error when invoking method")?
        .context("received empty response stream")?;

    let Some(response_wrapper::Response::GetPublicKeyResponse(_)) = response_wrapper.response  else {
        return Err(anyhow::anyhow!("response_wrapper does not have a valid invoke_response message"))
    };

    Ok(())
}

pub struct TestEvidenceProviderServer {}

#[tonic::async_trait]
impl StreamingSession for TestEvidenceProviderServer {
    type StreamStream = Pin<Box<dyn Stream<Item = Result<ResponseWrapper, Status>> + Send>>;

    async fn stream(
        &self,
        request: Request<Streaming<RequestWrapper>>,
    ) -> Result<Response<Self::StreamStream>, tonic::Status> {
        let mut request_stream = request.into_inner();
        let request = request_stream
            .next()
            .await
            .ok_or_else(|| tonic::Status::invalid_argument("empty request stream"))?
            .map_err(|err| {
                tonic::Status::internal(format!("error reading message from request stream: {err}"))
            })?;

        let Some(request_wrapper::Request::GetPublicKeyRequest(_)) = request.request else {
            return Err(tonic::Status::invalid_argument("request wrapper must have get_public_key_request field set"));
        };

        // TODO(#3641): Respond with a more interesting AttestationEvidence.
        let attestation_evidence = Some(AttestationEvidence::default());
        Ok(Response::new(Box::pin(futures::stream::iter(vec![Ok(
            ResponseWrapper {
                response: Some(response_wrapper::Response::GetPublicKeyResponse(
                    GetPublicKeyResponse {
                        attestation_evidence,
                    },
                )),
            },
        )]))))
    }
}
