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

use alloc::{sync::Arc, vec::Vec};
use anyhow::Context;
use oak_crypto::{
    encryptor::{
        AsyncRecipientContextGenerator, AsyncServerEncryptor, RecipientContextGenerator,
        ServerEncryptor,
    },
    proto::oak::crypto::v1::{EncryptedRequest, EncryptedResponse},
};

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// Information about a public key.
#[derive(Debug, Clone)]
pub struct PublicKeyInfo {
    /// The serialized public key.
    pub public_key: Vec<u8>,
    /// The serialized attestation report that binds the public key to the specific version of the
    /// code running in a TEE.
    pub attestation: Vec<u8>,
}

/// Wraps a closure to an underlying function with request encryption and response decryption logic,
/// based on the provided encryption key.
pub struct EncryptionHandler<H: FnOnce(Vec<u8>) -> Vec<u8>> {
    // TODO(#3442): Use attester to attest to the public key.
    encryption_key_provider: Arc<dyn RecipientContextGenerator>,
    request_handler: H,
}

impl<H: FnOnce(Vec<u8>) -> Vec<u8>> EncryptionHandler<H> {
    pub fn create(
        encryption_key_provider: Arc<dyn RecipientContextGenerator>,
        request_handler: H,
    ) -> Self {
        Self {
            encryption_key_provider,
            request_handler,
        }
    }
}

impl<H: FnOnce(Vec<u8>) -> Vec<u8>> EncryptionHandler<H> {
    pub fn invoke(self, encrypted_request: &EncryptedRequest) -> anyhow::Result<EncryptedResponse> {
        // Initialize server encryptor.
        let serialized_encapsulated_public_key = encrypted_request
            .serialized_encapsulated_public_key
            .as_ref()
            .context("initial request message doesn't contain encapsulated public key")?;
        let mut server_encryptor = ServerEncryptor::create(
            serialized_encapsulated_public_key,
            self.encryption_key_provider.clone(),
        )
        .context("couldn't create server encryptor")?;

        // Decrypt request.
        let (request, _) = server_encryptor
            .decrypt(encrypted_request)
            .context("couldn't decrypt request")?;

        // Handle request.
        let response = (self.request_handler)(request);

        // Encrypt and serialize response.
        // The resulting decryptor for subsequent requests is discarded because we don't expect
        // another message from the stream.
        server_encryptor
            .encrypt(&response, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt response")
    }
}

/// Wraps a closure to an underlying function with request encryption and response decryption logic,
/// based on the provided encryption key.
/// [`AsyncEncryptionHandler`] can be used when an [`AsyncRecipientContextGenerator`] is needed.
pub struct AsyncEncryptionHandler<G, H>
where
    G: AsyncRecipientContextGenerator + Send + Sync,
    H: FnOnce(Vec<u8>) -> Vec<u8>,
{
    // TODO(#3442): Use attester to attest to the public key.
    recipient_context_generator: Arc<G>,
    request_handler: H,
}

impl<G, H> AsyncEncryptionHandler<G, H>
where
    G: AsyncRecipientContextGenerator + Send + Sync,
    H: FnOnce(Vec<u8>) -> Vec<u8>,
{
    pub fn create(recipient_context_generator: Arc<G>, request_handler: H) -> Self {
        Self {
            recipient_context_generator,
            request_handler,
        }
    }

    pub async fn invoke(
        self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<EncryptedResponse> {
        // Initialize server encryptor.
        let mut server_encryptor =
            AsyncServerEncryptor::new(self.recipient_context_generator.as_ref());

        // Decrypt request.
        let (request, _associated_data) = server_encryptor
            .decrypt(encrypted_request)
            .await
            .context("couldn't decrypt request")?;

        // Handle request.
        let response = (self.request_handler)(request);

        // Encrypt and serialize response.
        // The resulting decryptor for consequent requests is discarded because we don't expect
        // another message from the stream.
        server_encryptor
            .encrypt(&response, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt response")
    }
}
