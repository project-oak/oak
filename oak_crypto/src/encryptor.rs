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

//! Implementation of the Bidirectional Hybrid Public Key Encryption (HPKE)
//!
//! scheme from RFC9180. <https://www.rfc-editor.org/rfc/rfc9180.html>
//! <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>

use alloc::vec::Vec;

use anyhow::Context;
use oak_proto_rust::oak::{
    crypto::v1::{AeadEncryptedMessage, EncryptedRequest, EncryptedResponse},
    session::v1::{EncryptedMessage, PlaintextMessage},
};

use crate::{
    encryption_key::{AsyncEncryptionKeyHandle, EncryptionKeyHandle},
    hpke::{
        deserialize_nonce, generate_random_nonce, setup_base_sender, RecipientContext,
        SenderContext, OAK_HPKE_INFO,
    },
};

#[derive(Debug, Clone)]
pub struct Payload {
    pub message: Vec<u8>,
    pub aad: Option<Vec<u8>>,
    pub nonce: Option<Vec<u8>>,
}

impl From<Vec<u8>> for Payload {
    fn from(message: Vec<u8>) -> Self {
        Payload { message, aad: None, nonce: None }
    }
}

impl From<(Vec<u8>, Vec<u8>)> for Payload {
    fn from(message_and_nonce: (Vec<u8>, Vec<u8>)) -> Self {
        Payload { message: message_and_nonce.0, aad: None, nonce: Some(message_and_nonce.1) }
    }
}

impl From<PlaintextMessage> for Payload {
    fn from(value: PlaintextMessage) -> Self {
        Payload { message: value.plaintext, nonce: None, aad: None }
    }
}

impl From<Payload> for PlaintextMessage {
    fn from(value: Payload) -> Self {
        PlaintextMessage { plaintext: value.message }
    }
}

impl From<EncryptedMessage> for Payload {
    fn from(value: EncryptedMessage) -> Self {
        Payload { message: value.ciphertext, nonce: value.nonce, aad: value.associated_data }
    }
}

impl From<Payload> for EncryptedMessage {
    fn from(value: Payload) -> Self {
        EncryptedMessage {
            ciphertext: value.message,
            nonce: value.nonce,
            associated_data: value.aad,
        }
    }
}

pub trait Encryptor: Send {
    fn encrypt(&mut self, plaintext: Payload) -> anyhow::Result<Payload>;
    fn decrypt(&mut self, ciphertext: Payload) -> anyhow::Result<Payload>;
}

/// Encryptor object for encrypting requests/decrypting responses.
///
/// Provides an encryptor for encrypting requests sent to the server and
/// decrypting server responses that are received by the client. Each Encryptor
/// object corresponds to a single crypto session between the client and the
/// server.
///
/// Sequence numbers for requests and responses are incremented separately,
/// meaning that there could be multiple responses per request and multiple
/// requests per response.
pub struct ClientEncryptor {
    /// Encapsulated public key needed to establish a symmetric session key.
    /// Only sent in the initial request message of the session.
    serialized_encapsulated_public_key: Option<Vec<u8>>,
    sender_context: SenderContext,
}

impl ClientEncryptor {
    /// Creates an HPKE crypto context by generating an new ephemeral key pair.
    /// The `serialized_server_public_key` must be a NIST P-256 SEC1 encoded
    /// point public key. <https://secg.org/sec1-v2.pdf>
    pub fn create(serialized_server_public_key: &[u8]) -> anyhow::Result<Self> {
        let (serialized_encapsulated_public_key, sender_context) =
            setup_base_sender(serialized_server_public_key, OAK_HPKE_INFO)
                .context("setting up base sender")?;
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
        let nonce = generate_random_nonce();
        let ciphertext = self
            .sender_context
            .seal(&nonce, plaintext, associated_data)
            .context("sealing request")?;

        Ok(EncryptedRequest {
            encrypted_message: Some(AeadEncryptedMessage {
                nonce: nonce.to_vec(),
                ciphertext,
                associated_data: associated_data.to_vec(),
            }),
            // Encapsulated public key is only sent in the initial request message of the session.
            serialized_encapsulated_public_key: self.serialized_encapsulated_public_key.take(),
        })
    }

    /// Decrypts a [`EncryptedResponse`] proto message using AEAD.
    /// Returns a response message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn decrypt(
        &self,
        encrypted_response: &EncryptedResponse,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encrypted_message = encrypted_response
            .encrypted_message
            .as_ref()
            .context("response doesn't contain encrypted message")?;
        let nonce = deserialize_nonce(&encrypted_message.nonce).context("deserializing nonce")?;

        let plaintext = self
            .sender_context
            .open(&nonce, &encrypted_message.ciphertext, &encrypted_message.associated_data)
            .context("decrypting response")?;
        Ok((plaintext, encrypted_message.associated_data.to_vec()))
    }
}

/// Encryptor object for encrypting responses/decrypting requests.
///
/// Encryptor object for decrypting client requests that are received by the
/// server and encrypting server responses that will be sent back to the client.
/// Each Encryptor object corresponds to a single crypto session between the
/// client and the server.
///
/// Sequence numbers for requests and responses are incremented separately,
/// meaning that there could be multiple responses per request and multiple
/// requests per response.
pub struct ServerEncryptor {
    recipient_context: RecipientContext,
}

impl ServerEncryptor {
    /// Decrypts a [`EncryptedRequest`] proto message using AEAD.
    /// Returns a response encryptor, the message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn decrypt<E: EncryptionKeyHandle + ?Sized>(
        encrypted_request: &EncryptedRequest,
        encryption_key_handle: &E,
    ) -> anyhow::Result<(Self, Vec<u8>, Vec<u8>)> {
        let serialized_encapsulated_public_key = encrypted_request
            .serialized_encapsulated_public_key
            .as_ref()
            .context("initial request message doesn't contain encapsulated public key")?;
        let recipient_context = encryption_key_handle
            .generate_recipient_context(serialized_encapsulated_public_key)
            .context("generating recipient context")?;
        let encryptor = Self { recipient_context };
        let (plaintext, associated_data) = encryptor.decrypt_inner(encrypted_request)?;
        Ok((encryptor, plaintext, associated_data))
    }

    /// Decrypts a [`EncryptedRequest`] proto message using AEAD.
    /// Returns a response encryptor, the message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    // TODO(#4311): Merge `decrypt` and `decrypt_async` once there is `async`
    // support in the Restricted Kernel.
    pub async fn decrypt_async<E: AsyncEncryptionKeyHandle + ?Sized>(
        encrypted_request: &EncryptedRequest,
        encryption_key_handle: &E,
    ) -> anyhow::Result<(Self, Vec<u8>, Vec<u8>)> {
        let serialized_encapsulated_public_key = encrypted_request
            .serialized_encapsulated_public_key
            .as_ref()
            .context("initial request message doesn't contain encapsulated public key")?;
        let recipient_context = encryption_key_handle
            .generate_recipient_context(serialized_encapsulated_public_key)
            .await
            .context("generating recipient context")?;
        let encryptor = Self { recipient_context };
        let (plaintext, associated_data) = encryptor.decrypt_inner(encrypted_request)?;
        Ok((encryptor, plaintext, associated_data))
    }

    pub fn new(recipient_context: RecipientContext) -> Self {
        Self { recipient_context }
    }

    fn decrypt_inner(
        &self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encrypted_message = encrypted_request
            .encrypted_message
            .as_ref()
            .context("request doesn't contain encrypted message")?;
        let nonce = deserialize_nonce(&encrypted_message.nonce).context("deserializing nonce")?;

        let plaintext = self
            .recipient_context
            .open(&nonce, &encrypted_message.ciphertext, &encrypted_message.associated_data)
            .context("decrypting request")?;
        Ok((plaintext, encrypted_message.associated_data.to_vec()))
    }

    /// Encrypts `plaintext` and authenticates `associated_data` using AEAD.
    /// Returns a [`EncryptedResponse`] proto message.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn encrypt(
        self,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<EncryptedResponse> {
        let nonce = generate_random_nonce();
        let ciphertext = self
            .recipient_context
            .seal(&nonce, plaintext, associated_data)
            .context("sealing response")?;

        Ok(EncryptedResponse {
            encrypted_message: Some(AeadEncryptedMessage {
                nonce: nonce.to_vec(),
                ciphertext,
                associated_data: associated_data.to_vec(),
            }),
        })
    }
}
