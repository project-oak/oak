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

pub mod proto {
    #![allow(clippy::return_self_not_must_use)]
    tonic::include_proto!("oak.session.noninteractive.v1");
}

pub mod transport;
pub mod verifier;

use crate::transport::AsyncEvidenceProvider;
use anyhow::{anyhow, Context};
use oak_crypto::{
    schema::{AeadEncryptedMessage, HpkeRequest, HpkeResponse},
    SenderCryptoProvider,
};
use prost::Message;
use std::vec::Vec;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// Client for connecting to Oak.
/// Represents a Relying Party from the RATS Architecture:
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-relying-party>
pub struct OakClient<T>
where
    T: micro_rpc::AsyncTransport<Error = anyhow::Error>,
{
    transport: T,
    crypto_provider: SenderCryptoProvider,
}

impl<T> OakClient<T>
where
    T: micro_rpc::AsyncTransport<Error = anyhow::Error> + AsyncEvidenceProvider,
{
    pub async fn create(mut transport: T) -> anyhow::Result<Self> {
        // TODO(#3442): Fetch enclave public key.
        // TODO(#3641): Implement client-side attestation verification.
        let evidence = transport
            .get_evidence()
            .await
            .context("couldn't get attestation evidence")?;
        let crypto_provider = SenderCryptoProvider::new(&evidence.encryption_public_key);
        Ok(Self {
            transport,
            crypto_provider,
        })
    }

    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // Create encryptor.
        let (serialized_encapsulated_public_key, request_encryptor) = self
            .crypto_provider
            .create_encryptor()
            .context("couldn't create encryptor")?;

        // Encrypt and serialize request.
        let (request_ciphertext, response_decryptor) = request_encryptor
            .encrypt(request_body, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt request")?;

        let request = HpkeRequest {
            encrypted_message: Some(AeadEncryptedMessage {
                ciphertext: request_ciphertext,
                associated_data: EMPTY_ASSOCIATED_DATA.to_vec(),
            }),
            serialized_encapsulated_public_key: Some(serialized_encapsulated_public_key),
        };
        let mut serialized_request = vec![];
        request
            .encode(&mut serialized_request)
            .map_err(|error| anyhow!("couldn't serialize request: {:?}", error))?;

        // Send request.
        let serialized_response = self
            .transport
            .invoke(&serialized_request)
            .await
            .map_err(|error| anyhow!("couldn't send request: {:?}", error))?;

        // Deserialize and decrypt response.
        let response = HpkeResponse::decode(serialized_response.as_ref())
            .map_err(|error| anyhow!("couldn't deserialize response: {:?}", error))?;
        let encrypted_message = response
            .encrypted_message
            .context("response doesn't contain encrypted message")?;
        // The resulting encryptor for subsequent requests is discarded because we don't send
        // another message to the stream.
        let (response_plaintext, _) = response_decryptor
            .decrypt(
                &encrypted_message.ciphertext,
                &encrypted_message.associated_data,
            )
            .context("couldn't decrypt response")?;

        Ok(response_plaintext)
    }
}
