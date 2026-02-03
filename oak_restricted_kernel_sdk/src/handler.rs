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
    EMPTY_ASSOCIATED_DATA, encryption_key::EncryptionKeyHandle, encryptor::ServerEncryptor,
};
use oak_proto_rust::oak::crypto::v1::{EncryptedRequest, EncryptedResponse};

/// Wraps a closure to an underlying function with request encryption and
/// response decryption logic, based on the provided encryption key.
pub struct EncryptionHandler<H: FnOnce(Vec<u8>) -> Vec<u8>> {
    encryption_key_handle: Arc<dyn EncryptionKeyHandle>,
    request_handler: H,
}

impl<H: FnOnce(Vec<u8>) -> Vec<u8>> EncryptionHandler<H> {
    pub fn create(encryption_key_handle: Arc<dyn EncryptionKeyHandle>, request_handler: H) -> Self {
        Self { encryption_key_handle, request_handler }
    }
}

impl<H: FnOnce(Vec<u8>) -> Vec<u8>> EncryptionHandler<H> {
    pub fn invoke(self, encrypted_request: &EncryptedRequest) -> anyhow::Result<EncryptedResponse> {
        // Decrypt request.
        let (server_encryptor, request, _) =
            ServerEncryptor::decrypt(encrypted_request, self.encryption_key_handle.as_ref())
                .context("couldn't create server encryptor")?;

        // Handle request.
        let response = (self.request_handler)(request);

        // Encrypt and serialize response.
        // The resulting decryptor for subsequent requests is discarded because we don't
        // expect another message from the stream.
        server_encryptor
            .encrypt(&response, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt response")
    }
}
