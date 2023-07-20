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

use crate::{
    hpke::aead::{AeadKey, AeadNonce, AEAD_ALGORITHM_KEY_SIZE_BYTES, AEAD_NONCE_SIZE_BYTES},
    util::{i2osp, xor},
};
use alloc::vec::Vec;
use anyhow::{anyhow, Context};
use hpke::{
    aead::{AeadCtxR, AeadCtxS, AesGcm256},
    kdf::HkdfSha256,
    kem::X25519HkdfSha256,
    Deserializable, Kem as KemTrait, OpModeR, OpModeS, Serializable,
};
use rand_core::OsRng;

type Aead = AesGcm256;
type Kdf = HkdfSha256;
type Kem = X25519HkdfSha256;
pub(crate) type PrivateKey = <Kem as KemTrait>::PrivateKey;
pub(crate) type PublicKey = <Kem as KemTrait>::PublicKey;
pub(crate) type EncappedKey = <Kem as KemTrait>::EncappedKey;

/// Maximum sequence number which can fit in [`AEAD_NONCE_SIZE_BYTES`] bytes.
/// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
const MAX_SEQUENCE_NUMBER: u128 = (1 << (8 * AEAD_NONCE_SIZE_BYTES)) - 1;

pub(crate) struct KeyPair {
    pub(crate) private_key: PrivateKey,
    pub(crate) public_key: PublicKey,
}

impl KeyPair {
    /// Randomly generates a key pair.
    pub(crate) fn generate() -> Self {
        let (private_key, public_key) = Kem::gen_keypair(&mut OsRng);
        Self {
            private_key,
            public_key,
        }
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
) -> anyhow::Result<(Vec<u8>, SenderRequestContext, SenderResponseContext)> {
    let recipient_public_key = PublicKey::from_bytes(serialized_recipient_public_key)
        .map_err(|error| anyhow!("couldn't deserialize recipient public key: {}", error))?;

    let (encapped_key, sender_context) = hpke::setup_sender::<Aead, Kdf, Kem, _>(
        &OpModeS::Base,
        &recipient_public_key,
        info,
        &mut OsRng,
    )
    .map_err(|error| anyhow!("couldn't create sender context: {}", error))?;

    let mut response_key = [0u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
    sender_context
        .export(b"response_key", &mut response_key)
        .map_err(|error| anyhow!("couldn't export response key: {}", error))?;

    let mut response_base_nonce = [0u8; AEAD_NONCE_SIZE_BYTES];
    sender_context
        .export(b"response_nonce", &mut response_base_nonce)
        .map_err(|error| anyhow!("couldn't export response nonce: {}", error))?;

    Ok((
        encapped_key.to_bytes().to_vec(),
        SenderRequestContext {
            inner: sender_context,
        },
        SenderResponseContext {
            response_key,
            response_base_nonce,
            sequence_number: 0,
        },
    ))
}

/// Sets up an HPKE recipient by creating a recipient context.
/// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
pub(crate) fn setup_base_recipient(
    serialized_encapped_key: &[u8],
    recipient_key_pair: &KeyPair,
    info: &[u8],
) -> anyhow::Result<(RecipientRequestContext, RecipientResponseContext)> {
    let encapped_key = EncappedKey::from_bytes(serialized_encapped_key).map_err(|error| {
        anyhow!(
            "couldn't deserialize the encapsulated public key: {}",
            error
        )
    })?;

    let recipient_context = hpke::setup_receiver::<Aead, Kdf, Kem>(
        &OpModeR::Base,
        &recipient_key_pair.private_key,
        &encapped_key,
        info,
    )
    .map_err(|error| anyhow!("couldn't create recipient context: {}", error))?;

    let mut response_key = [0u8; AEAD_ALGORITHM_KEY_SIZE_BYTES];
    recipient_context
        .export(b"response_key", &mut response_key)
        .map_err(|error| anyhow!("couldn't export response key: {}", error))?;

    let mut response_base_nonce = [0u8; AEAD_NONCE_SIZE_BYTES];
    recipient_context
        .export(b"response_nonce", &mut response_base_nonce)
        .map_err(|error| anyhow!("couldn't export response nonce: {}", error))?;

    Ok((
        RecipientRequestContext {
            inner: recipient_context,
        },
        RecipientResponseContext {
            response_key,
            response_base_nonce,
            sequence_number: 0,
        },
    ))
}

pub(crate) struct SenderRequestContext {
    inner: AeadCtxS<Aead, Kdf, Kem>,
}

impl SenderRequestContext {
    /// Encrypts message with associated data using AEAD.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
    pub(crate) fn seal(
        &mut self,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        self.inner
            .seal(plaintext, associated_data)
            .map_err(|error| anyhow!("couldn't encrypt message: {}", error))
    }
}

pub(crate) struct RecipientRequestContext {
    inner: AeadCtxR<Aead, Kdf, Kem>,
}

impl RecipientRequestContext {
    /// Decrypts message and validates associated data using AEAD.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption>
    pub(crate) fn open(
        &mut self,
        ciphertext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        self.inner
            .open(ciphertext, associated_data)
            .map_err(|error| anyhow!("couldn't decrypt message: {}", error))
    }
}

pub(crate) struct SenderResponseContext {
    response_key: AeadKey,
    response_base_nonce: AeadNonce,
    /// Sequence number that is XORed with the base nonce values to get AEAD nonces.
    /// Is represented as [`u128`] because the [`AEAD_NONCE_SIZE_BYTES`] is 12 bytes.
    sequence_number: u128,
}

impl SenderResponseContext {
    /// Decrypts response message and validates associated data using AEAD as part of bidirectional
    /// communication.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
    pub(crate) fn open(
        &mut self,
        ciphertext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let nonce = compute_nonce(self.sequence_number, &self.response_base_nonce)
            .context("couldn't compute nonce")?;
        let plaintext =
            crate::hpke::aead::decrypt(&self.response_key, &nonce, ciphertext, associated_data)
                .context("couldn't decrypt response message")?;
        increment_sequence_number(&mut self.sequence_number)
            .context("couldn't increment sequence number")?;
        Ok(plaintext)
    }
}

pub(crate) struct RecipientResponseContext {
    response_key: AeadKey,
    response_base_nonce: AeadNonce,
    /// Sequence number that is XORed with the base nonce values to get AEAD nonces.
    /// Is represented as [`u128`] because the [`AEAD_NONCE_SIZE_BYTES`] is 12 bytes.
    sequence_number: u128,
}

impl RecipientResponseContext {
    /// Encrypts response message with associated data using AEAD as part of bidirectional
    /// communication.
    /// <https://www.rfc-editor.org/rfc/rfc9180.html#name-bidirectional-encryption>
    pub(crate) fn seal(
        &mut self,
        plaintext: &[u8],
        associated_data: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let nonce = compute_nonce(self.sequence_number, &self.response_base_nonce)
            .context("couldn't compute nonce")?;
        let ciphertext =
            crate::hpke::aead::encrypt(&self.response_key, &nonce, plaintext, associated_data)
                .context("couldn't encrypt response message")?;
        increment_sequence_number(&mut self.sequence_number)
            .context("couldn't increment sequence number")?;
        Ok(ciphertext)
    }
}

fn compute_nonce(sequence_number: u128, base_nonce: &AeadNonce) -> anyhow::Result<AeadNonce> {
    let sequence_number_bytes = i2osp::<AEAD_NONCE_SIZE_BYTES>(sequence_number)
        .context("couldn't convert sequence number to bytes")?;
    let nonce = xor::<AEAD_NONCE_SIZE_BYTES>(base_nonce, &sequence_number_bytes);
    Ok(nonce)
}

fn increment_sequence_number(sequence_number: &mut u128) -> anyhow::Result<()> {
    if *sequence_number >= MAX_SEQUENCE_NUMBER {
        return Err(anyhow!("reached message limit"));
    }
    *sequence_number = sequence_number
        .checked_add(1)
        .context("couldn't increment sequence number")?;
    Ok(())
}
