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
use futures::channel::mpsc;
use oak_grpc::oak::session::v1::streaming_session_client::StreamingSessionClient;
use oak_proto_rust::oak::{
    crypto::v1::{EncryptedRequest, EncryptedResponse},
    session::v1::{
        request_wrapper, response_wrapper, EndorsedEvidence, GetEndorsedEvidenceRequest,
        GetEndorsedEvidenceResponse, InvokeRequest, InvokeResponse, RequestWrapper,
        ResponseWrapper,
    },
};
use tonic::transport::Channel;

pub struct GrpcStreamingTransport {
    response_stream: tonic::Streaming<ResponseWrapper>,
    request_tx_channel: mpsc::Sender<RequestWrapper>,
}

impl GrpcStreamingTransport {
    pub async fn new(rpc_client: StreamingSessionClient<Channel>) -> anyhow::Result<Self> {
        let mut rpc_client = rpc_client;
        let (tx, rx) = mpsc::channel(10);

        let response_stream =
            rpc_client.stream(rx).await.context("couldn't send stream request")?.into_inner();

        Ok(Self { response_stream, request_tx_channel: tx })
    }

    async fn send_and_receive(
        &mut self,
        request: request_wrapper::Request,
    ) -> anyhow::Result<ResponseWrapper> {
        self.request_tx_channel
            .try_send(RequestWrapper { request: Some(request) })
            .context("Couldn't send request")?;
        self.response_stream
            .message()
            .await
            .context("received empty response stream")?
            .context("empty response")
    }
}

#[async_trait::async_trait]
pub trait Transport {
    async fn invoke(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<EncryptedResponse>;
}

#[async_trait::async_trait]
impl Transport for GrpcStreamingTransport {
    async fn invoke(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<EncryptedResponse> {
        let response_wrapper: ResponseWrapper = self
            .send_and_receive(request_wrapper::Request::InvokeRequest(InvokeRequest {
                encrypted_request: Some(encrypted_request.clone()),
            }))
            .await
            .context("Sending invoke request")?;

        match response_wrapper.response {
            Some(response_wrapper::Response::InvokeResponse(InvokeResponse {
                encrypted_response: Some(encrypted_response),
            })) => Ok(encrypted_response),
            _ => Err(anyhow::anyhow!(
                "response_wrapper does not have a valid invoke_response message"
            )),
        }
    }
}

#[async_trait::async_trait]
pub trait EvidenceProvider {
    async fn get_endorsed_evidence(&mut self) -> anyhow::Result<EndorsedEvidence>;
}

#[async_trait::async_trait]
impl EvidenceProvider for GrpcStreamingTransport {
    async fn get_endorsed_evidence(&mut self) -> anyhow::Result<EndorsedEvidence> {
        let response_wrapper = self
            .send_and_receive(request_wrapper::Request::GetEndorsedEvidenceRequest(
                GetEndorsedEvidenceRequest {},
            ))
            .await
            .context("Sending get_endorsed_evidence request")?;

        match response_wrapper.response {
            Some(response_wrapper::Response::GetEndorsedEvidenceResponse(
                GetEndorsedEvidenceResponse { endorsed_evidence: Some(endorsed_evidence) },
            )) => Ok(endorsed_evidence),
            _ => Err(anyhow::anyhow!(
                "response_wrapper does not have a valid invoke_response message"
            )),
        }
    }
}
