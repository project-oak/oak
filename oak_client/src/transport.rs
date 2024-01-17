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
use oak_crypto::proto::oak::crypto::v1::{EncryptedRequest, EncryptedResponse};
use tonic::transport::Channel;

use crate::proto::oak::session::v1::{
    request_wrapper, response_wrapper, streaming_session_client::StreamingSessionClient,
    AttestationBundle, GetPublicKeyRequest, InvokeRequest, RequestWrapper,
};

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
                #[allow(clippy::needless_update)]
                request: Some(request_wrapper::Request::InvokeRequest(InvokeRequest {
                    encrypted_request: Some(encrypted_request.clone()),
                    ..Default::default()
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
            .context("InvokeResponse does not include an encrypted message")
    }
}

#[async_trait::async_trait]
pub trait EvidenceProvider {
    async fn get_endorsed_evidence(&mut self) -> anyhow::Result<AttestationBundle>;
}

#[async_trait::async_trait]
impl EvidenceProvider for GrpcStreamingTransport {
    async fn get_endorsed_evidence(&mut self) -> anyhow::Result<AttestationBundle> {
        let mut response_stream = self
            .rpc_client
            .stream(futures_util::stream::iter(vec![RequestWrapper {
                // TODO(#3641): Rename the corresponding message to `GetEvidence`.
                request: Some(request_wrapper::Request::GetPublicKeyRequest(
                    GetPublicKeyRequest {},
                )),
            }]))
            .await
            .context("couldn't get endorsed evidence")?
            .into_inner();

        // Read the next (and only) message from the response stream.
        let response_wrapper = response_stream
            .message()
            .await
            .context("gRPC server error when requesting endorsed evidence")?
            .context("received empty response stream")?;

        let Some(response_wrapper::Response::GetPublicKeyResponse(get_endorsed_evidence_response)) =
            response_wrapper.response
        else {
            return Err(anyhow::anyhow!(
                "response_wrapper doesn't contain a valid get_endorsed_evidence_response message"
            ));
        };

        #[allow(deprecated)]
        get_endorsed_evidence_response
            .attestation_bundle
            .context("get_endorsed_evidence_response message doesn't contain the endorsed evidence")
    }
}
