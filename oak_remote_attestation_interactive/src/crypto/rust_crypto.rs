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

//! Implementation of the crypto primitives used for remote attestation based on the RustCrypto and
//! Dalek Elliptic Curve crates.

use crate::{
    crypto::{
        DecryptionKey, EncryptionKey, KeyNegotiatorType, AEAD_ALGORITHM_KEY_LENGTH,
        CLIENT_KEY_PURPOSE, KEY_AGREEMENT_ALGORITHM_KEY_LENGTH, KEY_DERIVATION_SALT, NONCE_LENGTH,
        SERVER_KEY_PURPOSE, SHA256_HASH_LENGTH, SIGNATURE_LENGTH, SIGNING_ALGORITHM_KEY_LENGTH,
    },
    message::EncryptedData,
};
use aes_gcm::{aead::AeadInPlace, Aes256Gcm, Key, KeyInit, Nonce};
use alloc::vec::Vec;
use anyhow::{anyhow, Context};
use core::convert::TryInto;
use hkdf::Hkdf;
use p256::{
    ecdsa::{
        signature::{Signer as P256Signer, Verifier as P256Verifier},
        SigningKey, VerifyingKey,
    },
    EncodedPoint,
};
use rand_core::{OsRng, RngCore};
use sha2::{Digest, Sha256};
use x25519_dalek::{EphemeralSecret, PublicKey};

const EMPTY_ADITIONAL_DATA: &[u8] = b"";

/// Implementation of Authenticated Encryption with Associated Data (AEAD).
///
/// <https://datatracker.ietf.org/doc/html/rfc5116>
///
/// This implementation uses separate keys for encrypting data and decrypting peer encrypted data.
/// Which means that this implementation uses the same key for encryption, which peer uses for
/// decryption.
///
/// It is necessary to prevent the Loopback Attack, where malicious network takes an outgoing packet
/// and feeds it back as an incoming packet.
pub struct AeadEncryptor {
    /// Key used for encrypting data.
    encryption_key: EncryptionKey,
    /// Key used for decrypting peer encrypted data.
    decryption_key: DecryptionKey,
}

impl AeadEncryptor {
    pub(crate) fn new(encryption_key: EncryptionKey, decryption_key: DecryptionKey) -> Self {
        Self {
            encryption_key,
            decryption_key,
        }
    }

    /// Encrypts `data` using `AeadEncryptor::encryption_key`.
    pub fn encrypt(&mut self, data: &[u8]) -> anyhow::Result<EncryptedData> {
        // Generate a random nonce.
        let nonce = Self::generate_nonce().context("couldn't generate nonce")?;
        let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&self.encryption_key.0));

        let mut encrypted_data = data.to_vec();
        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        // And the nonce is authenticated by the AEAD algorithm itself.
        // https://datatracker.ietf.org/doc/html/rfc5116#section-2.1
        cipher
            .encrypt_in_place(
                Nonce::from_slice(&nonce),
                EMPTY_ADITIONAL_DATA,
                &mut encrypted_data,
            )
            .map_err(|error| anyhow!("couldn't encrypt data: {:?}", error))?;

        Ok(EncryptedData::new(nonce, encrypted_data))
    }

    /// Decrypts and authenticates `data` using `AeadEncryptor::decryption_key`.
    /// `data` must contain an encrypted message prefixed with a random nonce of [`NONCE_LENGTH`]
    /// length.
    pub fn decrypt(&mut self, data: &EncryptedData) -> anyhow::Result<Vec<u8>> {
        let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&self.decryption_key.0));
        let mut decrypted_data = data.data.to_vec();
        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        // And the nonce is authenticated by the AEAD algorithm itself.
        // https://datatracker.ietf.org/doc/html/rfc5116#section-2.1
        cipher
            .decrypt_in_place(
                Nonce::from_slice(&data.nonce),
                EMPTY_ADITIONAL_DATA,
                &mut decrypted_data,
            )
            .map_err(|error| anyhow!("couldn't decrypt data: {:?}", error))?;
        Ok(decrypted_data.to_vec())
    }

    /// Generate a random nonce.
    fn generate_nonce() -> anyhow::Result<[u8; NONCE_LENGTH]> {
        get_random()
    }
}

/// Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
///
/// <https://datatracker.ietf.org/doc/html/rfc7748#section-6.1>
pub struct KeyNegotiator {
    type_: KeyNegotiatorType,
    private_key: EphemeralSecret,
}

impl KeyNegotiator {
    pub fn create(type_: KeyNegotiatorType) -> anyhow::Result<Self> {
        let private_key = EphemeralSecret::new(OsRng);
        Ok(Self { type_, private_key })
    }

    pub fn public_key(&self) -> anyhow::Result<[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH]> {
        let public_key = PublicKey::from(&self.private_key);
        Ok(public_key.to_bytes())
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
        peer_public_key: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    ) -> anyhow::Result<AeadEncryptor> {
        let (encryption_key, decryption_key) = self
            .derive_session_keys(peer_public_key)
            .context("couldn't derive session keys")?;
        let encryptor = AeadEncryptor::new(encryption_key, decryption_key);
        Ok(encryptor)
    }

    /// Implementation of the session keys derivation.
    /// Returns a tuple with an encryption key and a decryption key.
    pub(crate) fn derive_session_keys(
        self,
        peer_public_key: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    ) -> anyhow::Result<(EncryptionKey, DecryptionKey)> {
        let self_public_key = self.public_key().context("couldn't get self public key")?;
        let parsed_public_key = PublicKey::from(*peer_public_key);
        let key_material = self.private_key.diffie_hellman(&parsed_public_key);

        match self.type_ {
            // On the server side `self_public_key` is the server key.
            KeyNegotiatorType::Server => {
                let encryption_key = EncryptionKey(
                    Self::key_derivation_function(
                        key_material.as_bytes(),
                        SERVER_KEY_PURPOSE,
                        &self_public_key,
                        peer_public_key,
                    )
                    .context("couldn't derive decryption key")?,
                );
                let decryption_key = DecryptionKey(
                    Self::key_derivation_function(
                        key_material.as_bytes(),
                        CLIENT_KEY_PURPOSE,
                        &self_public_key,
                        peer_public_key,
                    )
                    .context("couldn't derive encryption key")?,
                );
                Ok((encryption_key, decryption_key))
            }
            // On the client side `peer_public_key` is the server key.
            KeyNegotiatorType::Client => {
                let encryption_key = EncryptionKey(
                    Self::key_derivation_function(
                        key_material.as_bytes(),
                        CLIENT_KEY_PURPOSE,
                        peer_public_key,
                        &self_public_key,
                    )
                    .context("couldn't derive decryption key")?,
                );
                let decryption_key = DecryptionKey(
                    Self::key_derivation_function(
                        key_material.as_bytes(),
                        SERVER_KEY_PURPOSE,
                        peer_public_key,
                        &self_public_key,
                    )
                    .context("couldn't derive encryption key")?,
                );
                Ok((encryption_key, decryption_key))
            }
        }
    }

    /// Derives a session key from `key_material` using HKDF.
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc5869>
    ///
    /// <https://datatracker.ietf.org/doc/html/rfc7748#section-6.1>
    ///
    /// In order to derive keys, uses the information string that consists of a purpose string, a
    /// server public key and a client public key (in that specific order).
    pub(crate) fn key_derivation_function(
        key_material: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
        key_purpose: &str,
        server_public_key: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
        client_public_key: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    ) -> anyhow::Result<[u8; AEAD_ALGORITHM_KEY_LENGTH]> {
        // Session key is derived from a purpose string and two public keys.
        let mut info = Vec::with_capacity(
            key_purpose.as_bytes().len() + server_public_key.len() + client_public_key.len(),
        );
        info.extend_from_slice(key_purpose.as_bytes());
        info.extend_from_slice(server_public_key);
        info.extend_from_slice(client_public_key);

        // Initialize key derivation function.
        let salt = KEY_DERIVATION_SALT.as_bytes();
        let kdf = Hkdf::<Sha256>::new(Some(salt), key_material);

        // Derive session key.
        let mut session_key: [u8; AEAD_ALGORITHM_KEY_LENGTH] = Default::default();
        kdf.expand(&info, &mut session_key).map_err(|error| {
            anyhow!(
                "Couldn't get the output of the HKDF-Expand operation: {:?}",
                error
            )
        })?;
        Ok(session_key)
    }
}

pub struct Signer {
    signing_key: SigningKey,
    verifying_key: VerifyingKey,
}

impl Signer {
    pub fn create() -> anyhow::Result<Self> {
        let signing_key = SigningKey::random(&mut signature::rand_core::OsRng);
        let verifying_key = VerifyingKey::from(&signing_key);

        Ok(Self {
            signing_key,
            verifying_key,
        })
    }

    pub fn public_key(&self) -> anyhow::Result<[u8; SIGNING_ALGORITHM_KEY_LENGTH]> {
        self.verifying_key
            .to_encoded_point(false)
            .as_bytes()
            .try_into()
            .map_err(anyhow::Error::msg)
            .context("incorrect public key length")
    }

    pub fn sign(&self, input: &[u8]) -> anyhow::Result<[u8; SIGNATURE_LENGTH]> {
        self.signing_key
            .try_sign(input)
            .map_err(|error| anyhow!("couldn't sign input: {:?}", error))?
            .as_ref()
            .try_into()
            .map_err(anyhow::Error::msg)
            .context("incorrect signature length")
    }
}

pub struct SignatureVerifier {
    verifying_key: VerifyingKey,
}

impl SignatureVerifier {
    pub fn new(public_key_bytes: &[u8; SIGNING_ALGORITHM_KEY_LENGTH]) -> anyhow::Result<Self> {
        let encoded_point =
            EncodedPoint::from_bytes(public_key_bytes).map_err(anyhow::Error::msg)?;
        let verifying_key =
            VerifyingKey::from_encoded_point(&encoded_point).map_err(anyhow::Error::msg)?;
        Ok(Self { verifying_key })
    }

    /// Verifies the signature validity.
    pub fn verify(&self, input: &[u8], signature: &[u8; SIGNATURE_LENGTH]) -> anyhow::Result<()> {
        let signature = signature[..].try_into().map_err(anyhow::Error::msg)?;
        self.verifying_key
            .verify(input, &signature)
            .map_err(|error| anyhow!("signature verification failed: {:?}", error))
    }
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> [u8; SHA256_HASH_LENGTH] {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hasher.finalize().into()
}

/// Generates a random vector of `size` bytes.
pub fn get_random<const L: usize>() -> anyhow::Result<[u8; L]> {
    let mut result: [u8; L] = [Default::default(); L];
    OsRng
        .try_fill_bytes(&mut result[..])
        .map_err(|error| anyhow!("couldn't create random value: {:?}", error))?;
    Ok(result)
}
