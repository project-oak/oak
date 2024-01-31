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

pub(crate) mod aead;

use alloc::vec::Vec;

use anyhow::{anyhow, Context};
use hpke::{
    aead::AesGcm256, kdf::HkdfSha256, kem::X25519HkdfSha256, Kem as KemTrait, OpModeR, OpModeS,
};
pub use hpke::{Deserializable, Serializable};
use rand_core::{OsRng, RngCore};

use crate::{
    hpke::aead::{AeadKey, AeadNonce, AEAD_ALGORITHM_KEY_SIZE_BYTES, AEAD_NONCE_SIZE_BYTES},
    proto::oak::crypto::v1::SessionKeys,
};

type Aead = AesGcm256;
type Kdf = HkdfSha256;
type Kem = X25519HkdfSha256;
pub type PrivateKey = <Kem as KemTrait>::PrivateKey;
pub type PublicKey = <Kem as KemTrait>::PublicKey;
pub(crate) type EncappedKey = <Kem as KemTrait>::EncappedKey;

pub fn gen_kem_keypair() -> (PrivateKey, PublicKey) {
    Kem::gen_keypair(&mut OsRng)
}

pub struct KeyPair {
    pub(crate) private_key: PrivateKey,
    pub(crate) public_key: PublicKey,
}

impl KeyPair {
    /// Randomly generates a key pair.
    pub fn generate() -> Self {
        let (private_key, public_key) = gen_kem_keypair();
        Self {
            private_key,
            public_key,
        }
    }

    pub fn new(private_key: PrivateKey, public_key: PublicKey) -> Self {
        Self {
            private_key,
            public_key,
        }
    }

    pub fn get_private_key(&self) -> Vec<u8> {
        self.private_key.to_bytes().to_vec()
    }

    /// Returns a NIST P-256 SEC1 encoded point public key.
    /// <https://secg.org/sec1-v2.pdf>
    pub fn get_serialized_public_key(&self) -> Vec<u8> {
        self.public_key.to_bytes().to_vec()
    }
}

/// Sets up an HPKE sender by generating an ephemeral keypair (and serializing the corresponding
/// public key) and creating a sender context.
/// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
pub(crate) fn setup_base_sender(
    serialized_recipient_public_key: &[u8],
    info: &[u8],
) -> anyhow::Result<(Vec<u8>, SenderContext)> {
    let recipient_public_key = PublicKey::from_bytes(serialized_recipient_public_key)
        .map_err(|error| anyhow!("couldn't deserialize recipient public key: {}", error))?;

    let (encapsulated_public_key, sender_context) = hpke::setup_sender::<Aead, Kdf, Kem, _>(
        &OpModeS::Base,
        &recipient_public_key,
        info,
        &mut OsRng,
    )
    .map_err(|error| anyhow!("couldn't create sender context: {}", error))?;

    // Derive request key and nonce.
    // This is a deviation from the HPKE RFC, because we are deriving both session request and
    // response keys from the exporter secret, instead of having a request key be directly derived
    // from the shared secret. This is required to be able to share session keys between the Kernel
    // and the Application via RPC.
    // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
    let mut request_key = [0u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
    sender_context
        .export(b"request_key", &mut request_key)
        .map_err(|error| anyhow!("couldn't export request key: {}", error))?;

    // Derive response key and nonce.
    let mut response_key = [0u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
    sender_context
        .export(b"response_key", &mut response_key)
        .map_err(|error| anyhow!("couldn't export response key: {}", error))?;

    Ok((
        encapsulated_public_key.to_bytes().to_vec(),
        SenderContext {
            request_key,
            response_key,
        },
    ))
}

/// Sets up an HPKE recipient by creating a recipient context.
/// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
pub(crate) fn setup_base_recipient(
    serialized_encapsulated_public_key: &[u8],
    recipient_key_pair: &KeyPair,
    info: &[u8],
) -> anyhow::Result<RecipientContext> {
    let encapsulated_public_key = EncappedKey::from_bytes(serialized_encapsulated_public_key)
        .map_err(|error| {
            anyhow!(
                "couldn't deserialize the encapsulated public key: {}",
                error
            )
        })?;

    let recipient_context = hpke::setup_receiver::<Aead, Kdf, Kem>(
        &OpModeR::Base,
        &recipient_key_pair.private_key,
        &encapsulated_public_key,
        info,
    )
    .map_err(|error| anyhow!("couldn't create recipient context: {}", error))?;

    // Derive request key and nonce.
    // This is a deviation from the HPKE RFC, because we are deriving both session request and
    // response keys from the exporter secret, instead of having a request key be directly derived
    // from the shared secret. This is required to be able to share session keys between the Kernel
    // and the Application via RPC.
    // <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
    let mut request_key = [0u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
    recipient_context
        .export(b"request_key", &mut request_key)
        .map_err(|error| anyhow!("couldn't export request key: {}", error))?;

    // Derive response key and nonce.
    let mut response_key = [0u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
    recipient_context
        .export(b"response_key", &mut response_key)
        .map_err(|error| anyhow!("couldn't export response key: {}", error))?;

    Ok(RecipientContext {
        request_key,
        response_key,
    })
}

pub struct SenderContext {
    request_key: AeadKey,
    response_key: AeadKey,
}

impl SenderContext {
    /// Encrypts request message with associated data using AEAD.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
    pub(crate) fn seal(
        &self,
        nonce: &AeadNonce,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let ciphertext =
            crate::hpke::aead::encrypt(&self.request_key, nonce, plaintext, associated_data)
                .context("couldn't encrypt request message")?;
        Ok(ciphertext)
    }

    /// Decrypts response message and validates associated data using AEAD as part of bidirectional
    /// communication.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
    pub(crate) fn open(
        &self,
        nonce: &AeadNonce,
        ciphertext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let plaintext =
            crate::hpke::aead::decrypt(&self.response_key, nonce, ciphertext, associated_data)
                .context("couldn't decrypt response message")?;
        Ok(plaintext)
    }
}

pub struct RecipientContext {
    request_key: AeadKey,
    response_key: AeadKey,
}

impl RecipientContext {
    /// Decrypts request message and validates associated data using AEAD.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
    pub(crate) fn open(
        &self,
        nonce: &AeadNonce,
        ciphertext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let plaintext =
            crate::hpke::aead::decrypt(&self.request_key, nonce, ciphertext, associated_data)
                .context("couldn't decrypt request message")?;
        Ok(plaintext)
    }

    /// Encrypts response message with associated data using AEAD as part of bidirectional
    /// communication.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
    pub(crate) fn seal(
        &self,
        nonce: &AeadNonce,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let ciphertext =
            crate::hpke::aead::encrypt(&self.response_key, nonce, plaintext, associated_data)
                .context("couldn't encrypt response message")?;
        Ok(ciphertext)
    }

    /// Serializes recipient context into a `SessionKeys` Protobuf message.
    pub fn serialize(self) -> anyhow::Result<SessionKeys> {
        Ok(SessionKeys {
            request_key: self.request_key.to_vec(),
            response_key: self.response_key.to_vec(),
        })
    }

    /// Deserializes recipient context from a `SessionKeys` Protobuf message.
    pub fn deserialize(context: SessionKeys) -> anyhow::Result<Self> {
        Ok(Self {
            request_key: context.request_key.try_into().map_err(|v: Vec<u8>| {
                anyhow!(
                    "incorrect request key size, expected {}, got {}",
                    AEAD_ALGORITHM_KEY_SIZE_BYTES,
                    v.len()
                )
            })?,
            response_key: context.response_key.try_into().map_err(|v: Vec<u8>| {
                anyhow!(
                    "incorrect response key size, expected {}, got {}",
                    AEAD_ALGORITHM_KEY_SIZE_BYTES,
                    v.len()
                )
            })?,
        })
    }
}

// Generate a random nonce for AEAD.
pub(crate) fn generate_random_nonce() -> AeadNonce {
    let mut nonce = AeadNonce::default();
    OsRng.fill_bytes(&mut nonce);
    nonce
}

pub(crate) fn deserialize_nonce(nonce: &[u8]) -> anyhow::Result<AeadNonce> {
    nonce.try_into().map_err(|_| {
        anyhow!(
            "incorrect nonce size, expected {}, found {}",
            AEAD_NONCE_SIZE_BYTES,
            nonce.len()
        )
    })
}
