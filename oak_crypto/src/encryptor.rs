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

//! Implementation of the Bidirectional Hybrid Public Key Encryption (HPKE) scheme from RFC9180.
//! <https://www.rfc-editor.org/rfc/rfc9180.html>
//! <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>

use crate::{
    hpke::{setup_base_recipient, setup_base_sender, KeyPair, RecipientContext, SenderContext},
    proto::oak::crypto::v1::{AeadEncryptedMessage, EncryptedRequest, EncryptedResponse},
};
use alloc::{sync::Arc, vec::Vec};
use anyhow::{anyhow, Context};

/// Info string used by Hybrid Public Key Encryption;
pub(crate) const OAK_HPKE_INFO: &[u8] = b"Oak Hybrid Public Key Encryption v1";

pub struct EncryptionKeyProvider {
    key_pair: KeyPair,
}

impl Default for EncryptionKeyProvider {
    fn default() -> Self {
        Self::new()
    }
}

impl EncryptionKeyProvider {
    /// Creates a crypto provider with a newly generated key pair.
    pub fn new() -> Self {
        Self {
            key_pair: KeyPair::generate(),
        }
    }

    /// Returns a NIST P-256 SEC1 encoded point public key.
    /// <https://secg.org/sec1-v2.pdf>
    pub fn get_serialized_public_key(&self) -> Vec<u8> {
        self.key_pair.get_serialized_public_key()
    }
}

pub trait RecipientContextGenerator {
    // TODO(#3841): Implement Oak Kernel Crypto API and return corresponding session keys instead.
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext>;
}

impl RecipientContextGenerator for EncryptionKeyProvider {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        setup_base_recipient(encapsulated_public_key, &self.key_pair, OAK_HPKE_INFO)
            .context("couldn't generate recipient crypto context")
    }
}

/// Encryptor object for encrypting client requests that will be sent to the server and decrypting
/// server responses that are received by the client. Each Encryptor object corresponds to a single
/// crypto session between the client and the server.
///
/// Sequence numbers for requests and responses are incremented separately, meaning that there could
/// be multiple responses per request and multiple requests per response.
pub struct ClientEncryptor {
    /// Encapsulated public key needed to establish a symmetric session key.
    /// Only sent in the initial request message of the session.
    serialized_encapsulated_public_key: Option<Vec<u8>>,
    sender_context: SenderContext,
}

impl ClientEncryptor {
    /// Creates an HPKE crypto context by generating an new ephemeral key pair.
    /// The `serialized_server_public_key` must be a NIST P-256 SEC1 encoded point public key.
    /// <https://secg.org/sec1-v2.pdf>
    pub fn create(serialized_server_public_key: &[u8]) -> anyhow::Result<Self> {
        let (serialized_encapsulated_public_key, sender_context) =
            setup_base_sender(serialized_server_public_key, OAK_HPKE_INFO)
                .context("couldn't create sender crypto context")?;
        Ok(Self {
            serialized_encapsulated_public_key: Some(serialized_encapsulated_public_key.to_vec()),
            sender_context,
        })
    }

    /// Encrypts `plaintext` and authenticates `associated_data` using AEAD.
    /// Returns a [`EncryptedRequest`] proto message.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn encrypt(
        &mut self,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<EncryptedRequest> {
        let ciphertext = self
            .sender_context
            .seal(plaintext, associated_data)
            .context("couldn't encrypt request")?;
        let request = EncryptedRequest {
            encrypted_message: Some(AeadEncryptedMessage {
                ciphertext,
                associated_data: associated_data.to_vec(),
            }),
            /// Encapsulated public key is only sent in the initial request message of the session.
            serialized_encapsulated_public_key: self.serialized_encapsulated_public_key.take(),
        };
        Ok(request)
    }

    /// Decrypts a [`EncryptedResponse`] proto message using AEAD.
    /// Returns a response message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn decrypt(
        &mut self,
        encrypted_response: &EncryptedResponse,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encrypted_message = encrypted_response
            .encrypted_message
            .as_ref()
            .context("response doesn't contain encrypted message")?;
        let plaintext = self
            .sender_context
            .open(
                &encrypted_message.ciphertext,
                &encrypted_message.associated_data,
            )
            .context("couldn't decrypt response")?;
        Ok((plaintext, encrypted_message.associated_data.to_vec()))
    }
}

/// Encryptor object for decrypting client requests that are received by the server and encrypting
/// server responses that will be sent back to the client. Each Encryptor object corresponds to a
/// single crypto session between the client and the server.
/// Encryptor state is initialized after receiving an initial request message containing client's
/// encapsulated public key.
///
/// Sequence numbers for requests and responses are incremented separately, meaning that there could
/// be multiple responses per request and multiple requests per response.
pub struct ServerEncryptor {
    recipient_context_generator: Arc<dyn RecipientContextGenerator>,
    recipient_context: Option<RecipientContext>,
}

impl ServerEncryptor {
    pub fn new(recipient_context_generator: Arc<dyn RecipientContextGenerator>) -> Self {
        Self {
            recipient_context_generator,
            recipient_context: None,
        }
    }

    /// Decrypts a [`EncryptedRequest`] proto message using AEAD.
    /// Returns a response message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn decrypt(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        match &mut self.recipient_context {
            Some(context) => Self::decrypt_with_context(encrypted_request, context),
            None => {
                let serialized_encapsulated_public_key = encrypted_request
                    .serialized_encapsulated_public_key
                    .as_ref()
                    .context("initial request message doesn't contain encapsulated public key")?;
                let mut recipient_context = self
                    .recipient_context_generator
                    .generate_recipient_context(serialized_encapsulated_public_key)
                    .context("couldn't generate recipient crypto context")?;
                let (plaintext, associated_data) =
                    Self::decrypt_with_context(encrypted_request, &mut recipient_context)?;
                self.recipient_context = Some(recipient_context);
                Ok((plaintext, associated_data))
            }
        }
    }

    fn decrypt_with_context(
        encrypted_request: &EncryptedRequest,
        context: &mut RecipientContext,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encrypted_message = encrypted_request
            .encrypted_message
            .as_ref()
            .context("request doesn't contain encrypted message")?;
        let plaintext = context
            .open(
                &encrypted_message.ciphertext,
                &encrypted_message.associated_data,
            )
            .context("couldn't decrypt request")?;
        Ok((plaintext, encrypted_message.associated_data.to_vec()))
    }

    /// Encrypts `plaintext` and authenticates `associated_data` using AEAD.
    /// Returns a [`EncryptedResponse`] proto message.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn encrypt(
        &mut self,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<EncryptedResponse> {
        match &mut self.recipient_context {
            Some(context) => {
                let ciphertext = context
                    .seal(plaintext, associated_data)
                    .context("couldn't encrypt response")?;
                let response = EncryptedResponse {
                    encrypted_message: Some(AeadEncryptedMessage {
                        ciphertext,
                        associated_data: associated_data.to_vec(),
                    }),
                };
                Ok(response)
            }
            None => Err(anyhow!(
                "couldn't encrypt response because crypto context is not initialized"
            )),
        }
    }
}
