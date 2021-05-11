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

use anyhow::anyhow;
use ring::{
    aead::{self, BoundKey},
    agreement, rand,
};

// `ring::aead` uses 96-bit (12-byte) nonces.
// https://briansmith.org/rustdoc/ring/aead/constant.NONCE_LEN.html
//
// TODO(#2087): Use a unique nonce for each message.
const NONCE: [u8; aead::NONCE_LEN] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
// Algorithm used for encrypting/decrypting messages.
// https://datatracker.ietf.org/doc/html/rfc5288
static AEAD_ALGORITHM: &aead::Algorithm = &aead::AES_256_GCM;
// Algorithm used for negotiating a session key.
// https://datatracker.ietf.org/doc/html/rfc7748
static KEY_AGREEMENT_ALGORITHM: &agreement::Algorithm = &agreement::X25519;

/// Nonce implementation used by [`AeadInterface`].
/// It returns a single nonce once and then only returns errors.
struct OneNonceSequence(Option<aead::Nonce>);

impl OneNonceSequence {
    fn new() -> Self {
        let nonce = aead::Nonce::assume_unique_for_key(NONCE);
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
    // Key used for encrypting data.
    sealing_key: aead::SealingKey<OneNonceSequence>,
    // Key used for decrypting data.
    opening_key: aead::OpeningKey<OneNonceSequence>,
}

impl AeadEncryptor {
    pub fn new(key: &[u8]) -> Self {
        // AES-GCM algorithm uses the same key is used for both encryption and decryption.
        // https://datatracker.ietf.org/doc/html/rfc5288
        let unbound_sealing_key = aead::UnboundKey::new(AEAD_ALGORITHM, &key).unwrap();
        let sealing_key = ring::aead::SealingKey::new(unbound_sealing_key, OneNonceSequence::new());

        let unbound_opening_key = aead::UnboundKey::new(AEAD_ALGORITHM, &key).unwrap();
        let opening_key = ring::aead::OpeningKey::new(unbound_opening_key, OneNonceSequence::new());

        Self {
            sealing_key,
            opening_key,
        }
    }

    /// Encrypts `data` using [`AeadEncryptor::sealing_key`].
    ///
    /// Additional authenticated data is not required for the remotely attested channel,
    /// since after session key is established client and server exchange messages with a
    /// single encrypted field.
    /// And the nonce is authenticated by the AEAD algorithm itself.
    /// https://datatracker.ietf.org/doc/html/rfc5116#section-2.1
    pub fn encrypt(&mut self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        let mut encrypted_data = data.to_vec();
        self.sealing_key
            .seal_in_place_append_tag(
                aead::Aad::from(vec![]),
                &mut encrypted_data,
            )
            .map_err(|error| anyhow!("Couldn't encrypt data: {:?}", error))?;
        Ok(encrypted_data)
    }

    /// Decrypts and authenticates `data` using [`AeadEncryptor::opening_key`].
    ///
    /// Additional authenticated data is not required for the remotely attested channel,
    /// since after session key is established client and server exchange messages with a
    /// single encrypted field.
    /// And the nonce is authenticated by the AEAD algorithm itself.
    /// https://datatracker.ietf.org/doc/html/rfc5116#section-2.1
    pub fn decrypt(&mut self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        let mut decrypted_data = data.to_vec();
        let decrypted_data = self
            .opening_key
            .open_in_place(
                aead::Aad::from(vec![]),
                &mut decrypted_data,
            )
            .map_err(|error| anyhow!("Couldn't decrypt data: {:?}", error))?;
        Ok(decrypted_data.to_vec())
    }
}

pub struct KeyNegotiator {
    private_key: agreement::EphemeralPrivateKey,
}

impl KeyNegotiator {
    pub fn create() -> anyhow::Result<Self> {
        let rng = rand::SystemRandom::new();
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
        let peer_public_key =
            agreement::UnparsedPublicKey::new(KEY_AGREEMENT_ALGORITHM, peer_public_key);
        let session_key = agreement::agree_ephemeral(
            self.private_key,
            &peer_public_key,
            ring::error::Unspecified,
            Self::kdf,
        )
        .map_err(|error| anyhow!("Couldn't derive session key: {:?}", error))?;
        Ok(session_key)
    }

    /// Derives a session key from `key_material`.
    fn kdf(key_material: &[u8]) -> Result<Vec<u8>, ring::error::Unspecified> {
        // TODO(#2100): Derive a session key not just from `key_material` but also from server's and
        // client's public keys.
        // https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
        Ok(key_material.to_vec())
    }
}
