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
    hpke::{
        deserialize_nonce, setup_base_recipient, setup_base_sender, KeyPair, PrivateKey, PublicKey,
        RecipientContext, SenderContext,
    },
    proto::oak::crypto::v1::{AeadEncryptedMessage, EncryptedRequest, EncryptedResponse},
};
use alloc::{boxed::Box, sync::Arc, vec::Vec};
use anyhow::{anyhow, Context};
use async_trait::async_trait;
use hpke::Deserializable;

/// Info string used by Hybrid Public Key Encryption;
pub(crate) const OAK_HPKE_INFO: &[u8] = b"Oak Hybrid Public Key Encryption v1";

pub struct EncryptionKeyProvider {
    key_pair: KeyPair,
}

impl Default for EncryptionKeyProvider {
    fn default() -> Self {
        Self::generate()
    }
}

impl TryFrom<&oak_dice::evidence::RestrictedKernelDiceData> for EncryptionKeyProvider {
    type Error = anyhow::Error;
    fn try_from(
        dice_data: &oak_dice::evidence::RestrictedKernelDiceData,
    ) -> Result<Self, Self::Error> {
        let claims = dice_data
            .evidence
            .application_keys
            .claims()
            .map_err(|err| {
                anyhow::anyhow!("couldn't parse encryption public key certificate: {err}")
            })?;
        let private_key = PrivateKey::from_bytes(
            &dice_data.application_private_keys.encryption_private_key
                [..oak_dice::evidence::X25519_PRIVATE_KEY_SIZE],
        )
        .map_err(|error| anyhow::anyhow!("couldn't deserialize private key: {}", error))?;
        let public_key = {
            let cose_key =
                oak_dice::cert::get_public_key_from_claims_set(&claims).map_err(|err| {
                    anyhow::anyhow!("couldn't get public key from certificate: {err}")
                })?;
            oak_dice::cert::cose_key_to_hpke_public_key(&cose_key)
                .map_err(|err| anyhow::anyhow!("couldn't extract public key: {err}"))?
        };
        let encryption_key_provider = EncryptionKeyProvider::new(
            private_key,
            PublicKey::from_bytes(&public_key)
                .map_err(|err| anyhow::anyhow!("couldn't decode public key: {err}"))?,
        );
        Ok(encryption_key_provider)
    }
}

// TODO(#4513): Merge `EncryptionKeyProvider` and `hpke::KeyPair` into `EncryptionKey`.
impl EncryptionKeyProvider {
    /// Creates a crypto provider with a newly generated key pair.
    pub fn generate() -> Self {
        Self {
            key_pair: KeyPair::generate(),
        }
    }

    pub fn new(private_key: PrivateKey, public_key: PublicKey) -> Self {
        Self {
            key_pair: KeyPair::new(private_key, public_key),
        }
    }

    pub fn get_private_key(&self) -> Vec<u8> {
        // TODO(#4513): Implement Rust protections for the private key.
        self.key_pair.get_private_key()
    }

    /// Returns a NIST P-256 SEC1 encoded point public key.
    /// <https://secg.org/sec1-v2.pdf>
    pub fn get_serialized_public_key(&self) -> Vec<u8> {
        self.key_pair.get_serialized_public_key()
    }
}

// This trait just aliases the `RecipientContextGenerator`, while using different naming
// as defined in the Oak SDK design doc.
// TODO(#3841): rename the relevant trait and struct in our crypto crates.
/// Generate [`SessionKeys`] for the provided public key.
pub trait EncryptionKeyHandle {
    fn generate_session_keys(&self, encapsulated_public_key: &[u8]) -> anyhow::Result<SessionKeys>;
}

// Alias this struct in order to conform to the naming outlined in the restricted kernel SDK design
// doc.
use crate::encryptor::RecipientContext as SessionKeys;

impl<T> RecipientContextGenerator for T
where
    T: EncryptionKeyHandle,
{
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<SessionKeys> {
        self.generate_session_keys(encapsulated_public_key)
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

#[async_trait]
pub trait AsyncRecipientContextGenerator {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext>;
}

#[async_trait]
impl AsyncRecipientContextGenerator for EncryptionKeyProvider {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        (self as &dyn RecipientContextGenerator).generate_recipient_context(encapsulated_public_key)
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
        let nonce = self
            .sender_context
            .generate_nonce()
            .context("couldn't generate nonce")?;
        let ciphertext = self
            .sender_context
            .seal(&nonce, plaintext, associated_data)
            .context("couldn't encrypt request")?;

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
        &mut self,
        encrypted_response: &EncryptedResponse,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encrypted_message = encrypted_response
            .encrypted_message
            .as_ref()
            .context("response doesn't contain encrypted message")?;
        let nonce =
            deserialize_nonce(&encrypted_message.nonce).context("couldn't deserialize nonce")?;

        let plaintext = self
            .sender_context
            .open(
                &nonce,
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
///
/// Sequence numbers for requests and responses are incremented separately, meaning that there could
/// be multiple responses per request and multiple requests per response.
pub struct ServerEncryptor {
    recipient_context: RecipientContext,
}

impl ServerEncryptor {
    pub fn create(
        serialized_encapsulated_public_key: &[u8],
        recipient_context_generator: Arc<dyn RecipientContextGenerator>,
    ) -> anyhow::Result<Self> {
        let recipient_context = recipient_context_generator
            .generate_recipient_context(serialized_encapsulated_public_key)
            .context("couldn't generate recipient crypto context")?;
        Ok(Self::new(recipient_context))
    }

    pub fn new(recipient_context: RecipientContext) -> Self {
        Self { recipient_context }
    }

    /// Decrypts a [`EncryptedRequest`] proto message using AEAD.
    /// Returns a response message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn decrypt(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let encrypted_message = encrypted_request
            .encrypted_message
            .as_ref()
            .context("request doesn't contain encrypted message")?;
        let nonce =
            deserialize_nonce(&encrypted_message.nonce).context("couldn't deserialize nonce")?;

        let plaintext = self
            .recipient_context
            .open(
                &nonce,
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
        let nonce = self
            .recipient_context
            .generate_nonce()
            .context("couldn't generate nonce")?;
        let ciphertext = self
            .recipient_context
            .seal(&nonce, plaintext, associated_data)
            .context("couldn't encrypt response")?;

        Ok(EncryptedResponse {
            encrypted_message: Some(AeadEncryptedMessage {
                nonce: nonce.to_vec(),
                ciphertext,
                associated_data: associated_data.to_vec(),
            }),
        })
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
// TODO(#4311): Merge `AsyncServerEncryptor` and `ServerEncryptor` once there is `async` support in
// the Restricted Kernel.
pub struct AsyncServerEncryptor<'a, G>
where
    G: AsyncRecipientContextGenerator + Send + Sync,
{
    recipient_context_generator: &'a G,
    inner: Option<ServerEncryptor>,
}

impl<'a, G> AsyncServerEncryptor<'a, G>
where
    G: AsyncRecipientContextGenerator + Send + Sync,
{
    pub fn new(recipient_context_generator: &'a G) -> Self {
        Self {
            recipient_context_generator,
            inner: None,
        }
    }

    /// Decrypts a [`EncryptedRequest`] proto message using AEAD.
    /// Returns a response message plaintext and associated data.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub async fn decrypt(
        &mut self,
        encrypted_request: &EncryptedRequest,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        match &mut self.inner {
            Some(inner) => inner.decrypt(encrypted_request),
            None => {
                let serialized_encapsulated_public_key = encrypted_request
                    .serialized_encapsulated_public_key
                    .as_ref()
                    .context("initial request message doesn't contain encapsulated public key")?;
                let recipient_context = self
                    .recipient_context_generator
                    .generate_recipient_context(serialized_encapsulated_public_key)
                    .await
                    .context("couldn't generate recipient crypto context")?;
                let mut inner = ServerEncryptor::new(recipient_context);
                let (plaintext, associated_data) = inner.decrypt(encrypted_request)?;
                self.inner = Some(inner);
                Ok((plaintext, associated_data))
            }
        }
    }

    /// Encrypts `plaintext` and authenticates `associated_data` using AEAD.
    /// Returns a [`EncryptedResponse`] proto message.
    /// <https://datatracker.ietf.org/doc/html/rfc5116>
    pub fn encrypt(
        &mut self,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<EncryptedResponse> {
        match &mut self.inner {
            Some(inner) => inner.encrypt(plaintext, associated_data),
            None => Err(anyhow!(
                "couldn't encrypt response because crypto context is not initialized"
            )),
        }
    }
}
