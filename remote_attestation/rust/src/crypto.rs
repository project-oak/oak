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

// Algorithm used for encrypting/decrypting messages.
// https://datatracker.ietf.org/doc/html/rfc5288
static AEAD_ALGORITHM: &aead::Algorithm = &aead::AES_256_GCM;
// Algorithm used for negotiating a session key.
// https://datatracker.ietf.org/doc/html/rfc7748
static KEY_AGREEMENT_ALGORITHM: &agreement::Algorithm = &agreement::X25519;
/// Salt used for key derivation with HKDF.
/// https://datatracker.ietf.org/doc/html/rfc5869
const KEY_DERIVATION_SALT: &str = "Remote Attestation Protocol v1";
/// Purpose string used for deriving server session keys with HKDF.
const SERVER_KEY_PURPOSE: &str = "Remote Attestation Protocol Server Session Key";
/// Purpose string used for deriving client session keys with HKDF.
const CLIENT_KEY_PURPOSE: &str = "Remote Attestation Protocol Client Session Key";

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
///
/// This implementation uses separate keys for encrypting data and decrypting peer encrypted data.
/// Which means that this implementation uses the same key for encryption, which peer uses for
/// decryption.
/// It is necessary to prevent the Loopback Attack, where malicious network takes an outgoing packet
/// and feeds it back as an incoming packet.
pub struct AeadEncryptor {
    /// Key used for encrypting data.
    encryption_key: Vec<u8>,
    /// Key used for decrypting peer encrypted data.
    decryption_key: Vec<u8>,
}

impl AeadEncryptor {
    pub fn new(encryption_key: Vec<u8>, decryption_key: Vec<u8>) -> Self {
        Self {
            encryption_key,
            decryption_key,
        }
    }

    /// Encrypts `data` using [`AeadEncryptor::key`].
    pub fn encrypt(&mut self, data: &[u8]) -> anyhow::Result<EncryptedData> {
        // Generate a random nonce.
        let nonce = Self::generate_nonce();

        // Bind `AeadEncryptor::key` to a `NONCE`.
        let unbound_sealing_key = aead::UnboundKey::new(AEAD_ALGORITHM, &self.encryption_key)
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
        let unbound_opening_key =
            aead::UnboundKey::new(AEAD_ALGORITHM, &self.decryption_key).unwrap();
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

    /// Derives session keys from self and peer public keys and creates an [`AeadEncryptor`].
    ///
    /// HKDF is used to derive both server and client session keys. The information string provided
    /// to HKDF consists of a purpose string, a server public key and a client public key (in that
    /// specific order).
    /// Server session key uses the [`SERVER_KEY_PURPOSE`] purpose string and client session key
    /// uses [`CLIENT_KEY_PURPOSE`].
    ///
    /// Depending on `encryptor_type` creates a different type of encryptor: either server encryptor
    /// or client encryptor.
    pub fn create_encryptor(
        self,
        peer_public_key: &[u8],
        encryptor_type: EncryptorType,
    ) -> anyhow::Result<AeadEncryptor> {
        let self_public_key = self.public_key()?;
        let (encryption_key, decryption_key) = agreement::agree_ephemeral(
            self.private_key,
            &agreement::UnparsedPublicKey::new(KEY_AGREEMENT_ALGORITHM, peer_public_key),
            ring::error::Unspecified,
            |key_material| {
                let peer_public_key = peer_public_key.as_ref().to_vec();
                match encryptor_type {
                    // On the server side `self_public_key` is the server key.
                    EncryptorType::Server => {
                        let encryption_key = Self::key_derivation_function(
                            key_material,
                            SERVER_KEY_PURPOSE,
                            &self_public_key,
                            &peer_public_key,
                        );
                        let decryption_key = Self::key_derivation_function(
                            key_material,
                            CLIENT_KEY_PURPOSE,
                            &self_public_key,
                            &peer_public_key,
                        );
                        Ok((encryption_key, decryption_key))
                    }
                    // On the client side `peer_public_key` is the server key.
                    EncryptorType::Client => {
                        let encryption_key = Self::key_derivation_function(
                            key_material,
                            CLIENT_KEY_PURPOSE,
                            &peer_public_key,
                            &self_public_key,
                        );
                        let decryption_key = Self::key_derivation_function(
                            key_material,
                            SERVER_KEY_PURPOSE,
                            &peer_public_key,
                            &self_public_key,
                        );
                        Ok((encryption_key, decryption_key))
                    }
                }
            },
        )
        .map_err(|error| anyhow!("Couldn't agree on a session key: {:?}", error))?;
        Ok(AeadEncryptor::new(
            encryption_key
                .map_err(|error| anyhow!("Couldn't derive encryption key: {:?}", error))?,
            decryption_key
                .map_err(|error| anyhow!("Couldn't derive decryption key: {:?}", error))?,
        ))
    }

    /// Derives a session key from `key_material` using HKDF.
    /// https://datatracker.ietf.org/doc/html/rfc5869
    /// https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
    ///
    /// In order to derive keys, uses the information string that consists of a purpose string, a
    /// server public key and a client public key (in that specific order).
    fn key_derivation_function(
        key_material: &[u8],
        key_purpose: &str,
        server_public_key: &[u8],
        client_public_key: &[u8],
    ) -> Result<Vec<u8>, ring::error::Unspecified> {
        // Session key is derived from a purpose string and two public keys.
        let info = vec![key_purpose.as_bytes(), server_public_key, client_public_key];

        // Initialize key derivation function.
        let salt = Salt::new(HKDF_SHA256, KEY_DERIVATION_SALT.as_bytes());
        let kdf = salt.extract(key_material);

        // Derive session key.
        let mut session_key = vec![0; AEAD_ALGORITHM.key_len()];
        let output_key_material = kdf.expand(&info, AEAD_ALGORITHM)?;
        output_key_material.fill(&mut session_key)?;
        Ok(session_key.to_vec())
    }
}

/// Defines the type of encryptor created by [`KeyNegotiator::create_encryptor`].
pub enum EncryptorType {
    /// Defines a server encryptor, which uses server session key for encryption and client session
    /// key for decryption.
    Server,
    /// Defines a client encryptor, which uses client session key for encryption and server session
    /// key for decryption.
    Client,
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(&input);
    hasher.finalize().to_vec()
}
