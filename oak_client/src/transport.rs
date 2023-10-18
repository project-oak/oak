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

use crate::proto::oak::session::v1::{
    request_wrapper, response_wrapper, streaming_session_client::StreamingSessionClient,
    AttestationEvidence, GetPublicKeyRequest, InvokeRequest, RequestWrapper,
};
use anyhow::Context;
use oak_crypto::proto::oak::crypto::v1::{EncryptedRequest, EncryptedResponse};
use tonic::transport::Channel;

pub struct GrpcStreamingTransport {
    rpc_client: StreamingSessionClient<Channel>,
}

impl GrpcStreamingTransport {
    pub fn new(rpc_client: StreamingSessionClient<Channel>) -> Self {
        Self { rpc_client }
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
        let mut response_stream = self
            .rpc_client
            .stream(futures_util::stream::iter(vec![RequestWrapper {
                request: Some(request_wrapper::Request::InvokeRequest(InvokeRequest {
                    encrypted_request: Some(encrypted_request.clone()),
                })),
            }]))
            .await
            .context("couldn't send invoke request")?
            .into_inner();

        // Read the next (and only) message from the response stream.
        let response_wrapper = response_stream
            .message()
            .await
            .context("gRPC server error when invoking method")?
            .context("received empty response stream")?;

        let Some(response_wrapper::Response::InvokeResponse(invoke_response)) =
            response_wrapper.response
        else {
            return Err(anyhow::anyhow!(
                "response_wrapper does not have a valid invoke_response message"
            ));
        };

        invoke_response
            .encrypted_response
            .context("no encrypted response provided")
    }
}

#[async_trait::async_trait]
pub trait EvidenceProvider {
    async fn get_evidence(&mut self) -> anyhow::Result<AttestationEvidence>;
}

#[async_trait::async_trait]
impl EvidenceProvider for GrpcStreamingTransport {
    async fn get_evidence(&mut self) -> anyhow::Result<AttestationEvidence> {
        let mut response_stream = self
            .rpc_client
            .stream(futures_util::stream::iter(vec![RequestWrapper {
                // TODO(#3641): Rename the corresponding message to `GetEvidence`.
                request: Some(request_wrapper::Request::GetPublicKeyRequest(
                    GetPublicKeyRequest {},
                )),
            }]))
            .await
            .context("couldn't get attestation evidence")?
            .into_inner();

        // Read the next (and only) message from the response stream.
        let response_wrapper = response_stream
            .message()
            .await
            .context("gRPC server error when requesting attestation evidence")?
            .context("received empty response stream")?;

        let Some(response_wrapper::Response::GetPublicKeyResponse(get_evidence_response)) =
            response_wrapper.response
        else {
            return Err(anyhow::anyhow!(
                "response_wrapper doesn't contain a valid get_evidence_response message"
            ));
        };

        get_evidence_response
            .attestation_bundle
            .context("get_evidence_response message doesn't contain an attestation bundle")?
            .attestation_evidence
            .context("get_evidence_response message doesn't contain an attestation evidence")
    }
}
