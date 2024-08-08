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

use anyhow::Context;
use oak_crypto::{encryption_key::AsyncEncryptionKeyHandle, encryptor::ServerEncryptor};
use oak_proto_rust::oak::{
    crypto::v1::{EncryptedRequest, EncryptedResponse},
    session::v1::{
        request_wrapper, response_wrapper, EndorsedEvidence, GetEndorsedEvidenceResponse,
        InvokeRequest, InvokeResponse, RequestWrapper, ResponseWrapper,
    },
};

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// An Oak trusted application will write an implementation of
/// `ApplicationHandler` that accepts a serialized request (including di)
#[async_trait::async_trait]
pub trait ApplicationHandler: Send + Sync {
    async fn handle(&self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// The state heeded to handle an Oak crypto session inside of a streaming
/// server handler. This structure contains the
/// server-implementation-independent functionality for encryption, and holds
/// the instance of the class that actually implements the application
/// logic.
pub struct OakSessionContext {
    encryption_key_handle: Box<dyn AsyncEncryptionKeyHandle + Send + Sync>,
    endorsed_evidence: EndorsedEvidence,
    application_handler: Box<dyn ApplicationHandler>,
}

impl OakSessionContext {
    pub fn new(
        encryption_key_handle: Box<dyn AsyncEncryptionKeyHandle + Send + Sync>,
        endorsed_evidence: EndorsedEvidence,
        application_handler: Box<dyn ApplicationHandler>,
    ) -> Self {
        Self { encryption_key_handle, endorsed_evidence, application_handler }
    }

    pub fn endorsed_evidence(&self) -> &EndorsedEvidence {
        &self.endorsed_evidence
    }

    /// Decrypts the request, passes it to the application handler, and
    /// encrypts the resulting response.
    async fn handle_encrypted_request(
        &self,
        encrypted_request: &Option<EncryptedRequest>,
    ) -> anyhow::Result<EncryptedResponse> {
        let encrypted_request =
            encrypted_request.as_ref().context("encrypted request wasn't present")?;

        // Associated data is ignored.
        let (server_encryptor, name_bytes, _) =
            ServerEncryptor::decrypt_async(encrypted_request, &*self.encryption_key_handle)
                .await
                .context("couldn't decrypt request")?;

        let response = self
            .application_handler
            .handle(&name_bytes)
            .await
            .context("application handler failed")?;

        server_encryptor
            .encrypt(&response, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt response")
    }

    /// Handles an incoming Oak request by either handling it internally if it's
    /// an Oak message, or passing it to the provided application handler if
    /// it's an application message.
    pub(crate) async fn handle_request(
        &self,
        request_wrapper: &RequestWrapper,
    ) -> anyhow::Result<ResponseWrapper> {
        let request = &request_wrapper
            .request
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("empty request message"))?;

        let response = match request {
            request_wrapper::Request::GetEndorsedEvidenceRequest(_) => {
                response_wrapper::Response::GetEndorsedEvidenceResponse(
                    GetEndorsedEvidenceResponse {
                        endorsed_evidence: Some(self.endorsed_evidence().clone()),
                    },
                )
            }
            request_wrapper::Request::InvokeRequest(InvokeRequest { encrypted_request }) => {
                let encrypted_response = self.handle_encrypted_request(encrypted_request).await?;
                response_wrapper::Response::InvokeResponse(InvokeResponse {
                    encrypted_response: Some(encrypted_response),
                })
            }
        };
        Ok(ResponseWrapper { response: Some(response) })
    }
}
