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
//!
//! TODO(#2741): Refactor this to share more code between the two runtimes.

extern crate alloc;

use alloc::{sync::Arc, vec, vec::Vec};
use anyhow::{anyhow, Context};
use oak_crypto::{
    schema::{AeadEncryptedMessage, HpkeRequest, HpkeResponse},
    RecipientCryptoProvider,
};
use oak_remote_attestation_noninteractive::Attester;
use prost::Message;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// Information about a public key.
#[derive(Debug, Clone)]
pub struct PublicKeyInfo {
    /// The serialized public key.
    pub public_key: Vec<u8>,
    /// The serialized attestation evidence that binds the public key to the specific version of
    /// the code running in a TEE.
    pub attestation_evidence: Vec<u8>,
}

pub trait Handler {
    fn handle(&mut self, request: &[u8]) -> anyhow::Result<Vec<u8>>;
}

pub trait AttestationHandler {
    fn message(&mut self, body: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn get_public_key_info(&self) -> anyhow::Result<PublicKeyInfo>;
}

pub struct AttestationSessionHandler<H: Handler> {
    // TODO(#3442): Use attestation generator to attest to the public key.
    attester: Arc<dyn Attester>,
    crypto_provider: RecipientCryptoProvider,
    request_handler: H,
}

impl<H: Handler> AttestationSessionHandler<H> {
    pub fn create(attester: Arc<dyn Attester>, request_handler: H) -> anyhow::Result<Self> {
        Ok(Self {
            attester: attester,
            crypto_provider: RecipientCryptoProvider::new(),
            request_handler,
        })
    }
}

impl<H: Handler> AttestationHandler for AttestationSessionHandler<H> {
    fn message(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // Deserialize request.
        let request = HpkeRequest::decode(request_body)
            .map_err(|error| anyhow!("couldn't deserialize request: {:?}", error))?;

        // Create decryptor.
        let serialized_encapsulated_public_key = request
            .serialized_encapsulated_public_key
            .context("request doesn't contain serialized encapsulated public key")?;
        let request_decryptor = self
            .crypto_provider
            .create_decryptor(&serialized_encapsulated_public_key)
            .context("couldn't create decryptor")?;

        // Decrypt request.
        let encrypted_message = request
            .encrypted_message
            .context("request doesn't contain encrypted message")?;
        let (request_plaintext, response_encryptor) = request_decryptor
            .decrypt(
                &encrypted_message.ciphertext,
                &encrypted_message.associated_data,
            )
            .context("couldn't decrypt request")?;

        // Handle request.
        let response_plaintext = self
            .request_handler
            .handle(&request_plaintext)
            .context("couldn't handle request")?;

        // Encrypt and serialize response.
        // The resulting decryptor for consequent requests is discarded because we don't expect
        // another message from the stream.
        let (response_ciphertext, _) = response_encryptor
            .encrypt(&response_plaintext, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt response")?;
        let response = HpkeResponse {
            encrypted_message: Some(AeadEncryptedMessage {
                ciphertext: response_ciphertext,
                associated_data: EMPTY_ASSOCIATED_DATA.to_vec(),
            }),
        };
        let mut serialized_response = vec![];
        response
            .encode(&mut serialized_response)
            .map_err(|error| anyhow!("couldn't serialize response: {:?}", error))?;

        Ok(serialized_response)
    }

    fn get_public_key_info(&self) -> anyhow::Result<PublicKeyInfo> {
        let public_key = self.crypto_provider.get_serialized_public_key();
        let attestation_evidence = self
            .attester
            .generate_attestation_evidence(&public_key)
            .context("couldn't generate attestation evidence")?;
        Ok(PublicKeyInfo {
            public_key,
            // TODO(#3640): Return attestation evidence.
            attestation_evidence: attestation_evidence.attestation_report,
        })
    }
}
