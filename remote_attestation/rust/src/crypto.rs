//
// Copyright 2021 The Project Oak Authors
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

use crate::proto::EncryptedData;
use anyhow::anyhow;
use ring::{
    aead::{self, BoundKey},
    agreement,
    hkdf::{Salt, HKDF_SHA256},
    rand::{SecureRandom, SystemRandom},
};
use sha2::{digest::Digest, Sha256};
use std::cmp::Ordering;

// Algorithm used for encrypting/decrypting messages.
// https://datatracker.ietf.org/doc/html/rfc5288
static AEAD_ALGORITHM: &aead::Algorithm = &aead::AES_256_GCM;
// Algorithm used for negotiating a session key.
// https://datatracker.ietf.org/doc/html/rfc7748
static KEY_AGREEMENT_ALGORITHM: &agreement::Algorithm = &agreement::X25519;
/// Salt used for key derivation with HKDF.
/// https://datatracker.ietf.org/doc/html/rfc5869
const HKDF_SALT: &str = "Remote Attestation Protocol v1";
/// Purpose string used for deriving session keys with HKDF.
const SESSION_KEY_PURPOSE: &str = "Remote Attestation Protocol Session Key";

/// Nonce implementation used by [`AeadEncryptor`].
/// It returns a single nonce once and then only returns errors.
struct OneNonceSequence(Option<aead::Nonce>);

impl OneNonceSequence {
    fn new(nonce: [u8; aead::NONCE_LEN]) -> Self {
        let nonce = aead::Nonce::assume_unique_for_key(nonce);
        Self(Some(nonce))
    }
}

impl aead::NonceSequence for OneNonceSequence {
    fn advance(&mut self) -> Result<aead::Nonce, ring::error::Unspecified> {
        self.0.take().ok_or(ring::error::Unspecified)
    }
}

/// Implementation of Authenticated Encryption with Associated Data (AEAD).
/// https://datatracker.ietf.org/doc/html/rfc5116
pub struct AeadEncryptor {
    /// Key used for encrypting and decrypting data.
    ///
    /// AES-GCM algorithm uses the same key for both encryption and decryption.
    /// https://datatracker.ietf.org/doc/html/rfc5288
    key: Vec<u8>,
}

impl AeadEncryptor {
    pub fn new(key: Vec<u8>) -> Self {
        Self { key }
    }

    /// Encrypts `data` using [`AeadEncryptor::key`].
    pub fn encrypt(&mut self, data: &[u8]) -> anyhow::Result<EncryptedData> {
        // Generate a random nonce.
        let nonce = Self::generate_nonce();

        // Bind `AeadEncryptor::key` to a `NONCE`.
        let unbound_sealing_key = aead::UnboundKey::new(AEAD_ALGORITHM, &self.key)
            .map_err(|error| anyhow!("Couldn't create sealing key: {:?}", error))?;
        let mut sealing_key =
            ring::aead::SealingKey::new(unbound_sealing_key, OneNonceSequence::new(nonce));

        let mut encrypted_data = data.to_vec();
        sealing_key
            // Additional authenticated data is not required for the remotely attested channel,
            // since after session key is established client and server exchange messages with a
            // single encrypted field.
            // And the nonce is authenticated by the AEAD algorithm itself.
            // https://datatracker.ietf.org/doc/html/rfc5116#section-2.1
            .seal_in_place_append_tag(aead::Aad::empty(), &mut encrypted_data)
            .map_err(|error| anyhow!("Couldn't encrypt data: {:?}", error))?;

        Ok(EncryptedData {
            nonce: nonce.to_vec(),
            data: encrypted_data,
        })
    }

    /// Decrypts and authenticates `data` using [`AeadEncryptor::key`].
    /// `data` must contain an encrypted message prefixed with a random nonce of [`aead::NONCE_LEN`]
    /// length.
    pub fn decrypt(&mut self, data: &EncryptedData) -> anyhow::Result<Vec<u8>> {
        // Extract nonce from `data`.
        let mut nonce: [u8; aead::NONCE_LEN] = Default::default();
        nonce.copy_from_slice(&data.nonce[0..aead::NONCE_LEN]);

        // Bind `AeadEncryptor::key` to the extracted `nonce`.
        let unbound_opening_key = aead::UnboundKey::new(AEAD_ALGORITHM, &self.key).unwrap();
        let mut opening_key =
            ring::aead::OpeningKey::new(unbound_opening_key, OneNonceSequence::new(nonce));

        let mut decrypted_data = data.data.to_vec();
        let decrypted_data = opening_key
            // Additional authenticated data is not required for the remotely attested channel,
            // since after session key is established client and server exchange messages with a
            // single encrypted field.
            // And the nonce is authenticated by the AEAD algorithm itself.
            // https://datatracker.ietf.org/doc/html/rfc5116#section-2.1
            .open_in_place(aead::Aad::empty(), &mut decrypted_data)
            .map_err(|error| anyhow!("Couldn't decrypt data: {:?}", error))?;
        Ok(decrypted_data.to_vec())
    }

    /// Generate a random nonce.
    /// `ring::aead` uses 96-bit (12-byte) nonces.
    /// https://briansmith.org/rustdoc/ring/aead/constant.NONCE_LEN.html
    fn generate_nonce() -> [u8; aead::NONCE_LEN] {
        let mut nonce: [u8; aead::NONCE_LEN] = Default::default();
        let rng = SystemRandom::new();
        rng.fill(&mut nonce).unwrap();
        nonce
    }
}

/// Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
/// https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
pub struct KeyNegotiator {
    private_key: agreement::EphemeralPrivateKey,
}

impl KeyNegotiator {
    pub fn create() -> anyhow::Result<Self> {
        let rng = ring::rand::SystemRandom::new();
        let private_key = agreement::EphemeralPrivateKey::generate(KEY_AGREEMENT_ALGORITHM, &rng)
            .map_err(|error| anyhow!("Couldn't generate private key: {:?}", error))?;
        Ok(Self { private_key })
    }

    pub fn public_key(&self) -> anyhow::Result<Vec<u8>> {
        let public_key = self
            .private_key
            .compute_public_key()
            .map_err(|error| anyhow!("Couldn't get public key: {:?}", error))?;
        Ok(public_key.as_ref().to_vec())
    }

    pub fn derive_session_key(self, peer_public_key: &[u8]) -> anyhow::Result<Vec<u8>> {
        let public_key = self.public_key()?;
        let session_key = agreement::agree_ephemeral(
            self.private_key,
            &agreement::UnparsedPublicKey::new(KEY_AGREEMENT_ALGORITHM, peer_public_key),
            ring::error::Unspecified,
            |key_material| {
                Self::key_derivation_function(
                    key_material,
                    &public_key,
                    &peer_public_key.as_ref().to_vec(),
                )
            },
        )
        .map_err(|error| anyhow!("Couldn't agree on a session key: {:?}", error))?;
        Ok(session_key)
    }

    /// Derives a session key from `key_material` using HKDF.
    /// https://datatracker.ietf.org/doc/html/rfc5869
    /// https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
    ///
    /// TODO(#2181): Use separate keys for server and client encryption.
    fn key_derivation_function(
        key_material: &[u8],
        public_key: &[u8],
        peer_public_key: &[u8],
    ) -> Result<Vec<u8>, ring::error::Unspecified> {
        // Session key is derived from a purpose string, public key and peer public key.
        let mut info = vec![];
        info.push(SESSION_KEY_PURPOSE.as_bytes());
        // Sort public keys so that keys derived on the both sides of the protocol are equal.
        if public_key.iter().cmp(peer_public_key.iter()) == Ordering::Less {
            info.push(public_key);
            info.push(peer_public_key);
        } else {
            info.push(peer_public_key);
            info.push(public_key);
        }

        // Initialize key derivation function.
        let salt = Salt::new(HKDF_SHA256, HKDF_SALT.as_bytes());
        let kdf = salt.extract(key_material);

        // Derive session key.
        let mut session_key = vec![0; AEAD_ALGORITHM.key_len()];
        let output_key_material = kdf.expand(&info, AEAD_ALGORITHM)?;
        output_key_material.fill(&mut session_key)?;
        Ok(session_key.to_vec())
    }
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(&input);
    hasher.finalize().to_vec()
}
