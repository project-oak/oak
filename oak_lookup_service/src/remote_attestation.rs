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

//! Server-side implementation the remote attestation handshake protocol.
//!
//! A simplified version of the implementation from the `oak_grpc_unary_attestation`
//! crate.
extern crate alloc;

use alloc::{sync::Arc, vec, vec::Vec};
use anyhow::{anyhow, Context};
use oak_crypto::{
    encryptor::{EncryptionKeyProvider, ServerEncryptor},
    proto::oak::crypto::v1::EncryptedRequest,
};
use oak_remote_attestation_interactive::handshaker::AttestationGenerator;
use prost::Message;

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

pub trait AttestationHandler: micro_rpc::Transport<Error = anyhow::Error> {
    fn get_public_key_info(&self) -> PublicKeyInfo;
}

pub struct AttestationSessionHandler<H: micro_rpc::Transport<Error = anyhow::Error>> {
    // TODO(#3442): Use attestation generator to attest to the public key.
    _attestation_generator: Arc<dyn AttestationGenerator>,
    encryption_key_provider: Arc<EncryptionKeyProvider>,
    request_handler: H,
}

impl<H: micro_rpc::Transport<Error = anyhow::Error>> AttestationSessionHandler<H> {
    pub fn create(
        attestation_generator: Arc<dyn AttestationGenerator>,
        request_handler: H,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            _attestation_generator: attestation_generator,
            encryption_key_provider: Arc::new(EncryptionKeyProvider::new()),
            request_handler,
        })
    }
}

impl<H: micro_rpc::Transport<Error = anyhow::Error>> micro_rpc::Transport
    for AttestationSessionHandler<H>
{
    type Error = anyhow::Error;
    fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        let mut server_encryptor = ServerEncryptor::new(self.encryption_key_provider.clone());

        // log::info!("request body: {:?}", request_body);
        // Deserialize and decrypt request.
        // let encrypted_request = EncryptedRequest::decode(request_body)
        //     .map_err(|error| anyhow!("couldn't deserialize request [{:?}]: {:?}", request_body, error))?;
        // let (request, _) = server_encryptor
        //     .decrypt(&encrypted_request)
        //     .context("couldn't decrypt request")?;

        // Handle request.
        let response_body = self
            .request_handler
            .invoke(&request_body)
            .context("couldn't handle request")?;

        // Encrypt and serialize response.
        // The resulting decryptor for consequent requests is discarded because we don't expect
        // another message from the stream.
        /*
        let encrypted_response = server_encryptor
            .encrypt(&response, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt response")?;
        let mut serialized_response = vec![];
        encrypted_response
            .encode(&mut serialized_response)
            .map_err(|error| anyhow!("couldn't serialize response: {:?}", error))?;
        */

        Ok(response_body)
    }
}

impl<H: micro_rpc::Transport<Error = anyhow::Error>> AttestationHandler
    for AttestationSessionHandler<H>
{
    fn get_public_key_info(&self) -> PublicKeyInfo {
        // TODO(#3442): Generate and return public key.
        PublicKeyInfo {
            public_key: self.encryption_key_provider.get_serialized_public_key(),
            attestation: Vec::new(),
        }
    }
}
