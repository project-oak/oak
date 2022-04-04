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

// Crypto primitives used by the remote attestation protocol.
//
// Should be kept in sync with the Java implementation of the remote attestation
// protocol.

use crate::message::EncryptedData;
use alloc::{format, vec, vec::Vec};
use anyhow::{anyhow, Context};
use core::convert::TryInto;
use ring::{
    aead::{self, BoundKey},
    agreement,
    digest::{digest, SHA256},
    hkdf::{Salt, HKDF_SHA256},
    rand::{SecureRandom, SystemRandom},
    signature::{EcdsaKeyPair, EcdsaSigningAlgorithm, EcdsaVerificationAlgorithm, KeyPair},
};

/// Length of the encryption nonce.
/// `ring::aead` uses 96-bit (12-byte) nonces.
/// <https://briansmith.org/rustdoc/ring/aead/constant.NONCE_LEN.html>
pub const NONCE_LENGTH: usize = aead::NONCE_LEN;
pub const SHA256_HASH_LENGTH: usize = 32;
/// Algorithm used for encrypting/decrypting messages.
/// <https://datatracker.ietf.org/doc/html/rfc5288>
static AEAD_ALGORITHM: &aead::Algorithm = &aead::AES_256_GCM;
pub const AEAD_ALGORITHM_KEY_LENGTH: usize = 32;
/// Algorithm used for negotiating a session key.
/// <https://datatracker.ietf.org/doc/html/rfc7748>
static KEY_AGREEMENT_ALGORITHM: &agreement::Algorithm = &agreement::X25519;
pub const KEY_AGREEMENT_ALGORITHM_KEY_LENGTH: usize = 32;
/// Salt used for key derivation with HKDF.
/// <https://datatracker.ietf.org/doc/html/rfc5869>
pub const KEY_DERIVATION_SALT: &str = "Remote Attestation Protocol v1";
/// Purpose string used for deriving server session keys with HKDF.
pub const SERVER_KEY_PURPOSE: &str = "Remote Attestation Protocol Server Session Key";
/// Purpose string used for deriving client session keys with HKDF.
pub const CLIENT_KEY_PURPOSE: &str = "Remote Attestation Protocol Client Session Key";
/// Algorithm used to create cryptographic signatures.
static SIGNING_ALGORITHM: &EcdsaSigningAlgorithm =
    &ring::signature::ECDSA_P256_SHA256_FIXED_SIGNING;
/// OpenSSL ECDSA-P256 key public key length, which is represented as
/// `0x04 | X: 32-byte | Y: 32-byte`.
/// Where X and Y are big-endian coordinates of an Elliptic Curve point.
/// <https://datatracker.ietf.org/doc/html/rfc6979>
pub const SIGNING_ALGORITHM_KEY_LENGTH: usize = 65;
// TODO(#2277): Use OpenSSL signature format (which is 72 bytes).
/// IEEE-P1363 encoded ECDSA-P256 signature length.
/// <https://datatracker.ietf.org/doc/html/rfc6979>
/// <https://standards.ieee.org/standard/1363-2000.html>
pub const SIGNATURE_LENGTH: usize = 64;
/// Algorithm used to verify cryptographic signatures.
static VERIFICATION_ALGORITHM: &EcdsaVerificationAlgorithm =
    &ring::signature::ECDSA_P256_SHA256_FIXED;

/// Nonce implementation used by [`AeadEncryptor`].
/// It returns a single nonce once and then only returns errors.
struct OneNonceSequence(Option<aead::Nonce>);

impl OneNonceSequence {
    fn new(nonce: [u8; NONCE_LENGTH]) -> Self {
        let nonce = aead::Nonce::assume_unique_for_key(nonce);
        Self(Some(nonce))
    }
}

impl aead::NonceSequence for OneNonceSequence {
    fn advance(&mut self) -> Result<aead::Nonce, ring::error::Unspecified> {
        self.0.take().ok_or(ring::error::Unspecified)
    }
}

/// Convenience struct for passing an encryption key as an argument.
#[derive(PartialEq)]
pub(crate) struct EncryptionKey(pub(crate) [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH]);

/// Convenience struct for passing a decryption key as an argument.
#[derive(PartialEq)]
pub(crate) struct DecryptionKey(pub(crate) [u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH]);

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
        let nonce = Self::generate_nonce().context("Couldn't generate nonce")?;

        // Bind [`AeadEncryptor::key`] to a `nonce`.
        let unbound_sealing_key = aead::UnboundKey::new(AEAD_ALGORITHM, &self.encryption_key.0)
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

        Ok(EncryptedData::new(nonce, encrypted_data))
    }

    /// Decrypts and authenticates `data` using `AeadEncryptor::decryption_key`.
    /// `data` must contain an encrypted message prefixed with a random nonce of [`NONCE_LENGTH`]
    /// length.
    pub fn decrypt(&mut self, data: &EncryptedData) -> anyhow::Result<Vec<u8>> {
        // Bind `AeadEncryptor::key` to the extracted `nonce`.
        let unbound_opening_key =
            aead::UnboundKey::new(AEAD_ALGORITHM, &self.decryption_key.0).unwrap();
        let mut opening_key =
            ring::aead::OpeningKey::new(unbound_opening_key, OneNonceSequence::new(data.nonce));

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
    fn generate_nonce() -> anyhow::Result<[u8; NONCE_LENGTH]> {
        get_random()
    }
}

/// Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
///
/// <https://datatracker.ietf.org/doc/html/rfc7748#section-6.1>
pub struct KeyNegotiator {
    type_: KeyNegotiatorType,
    private_key: agreement::EphemeralPrivateKey,
}

impl KeyNegotiator {
    pub fn create(type_: KeyNegotiatorType) -> anyhow::Result<Self> {
        let rng = ring::rand::SystemRandom::new();
        let private_key = agreement::EphemeralPrivateKey::generate(KEY_AGREEMENT_ALGORITHM, &rng)
            .map_err(|error| anyhow!("Couldn't generate private key: {:?}", error))?;
        Ok(Self { type_, private_key })
    }

    pub fn public_key(&self) -> anyhow::Result<[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH]> {
        let public_key = self
            .private_key
            .compute_public_key()
            .map_err(|error| anyhow!("Couldn't get public key: {:?}", error))?
            .as_ref()
            .to_vec();
        public_key
            .as_slice()
            .try_into()
            .map_err(anyhow::Error::msg)
            .context(format!(
                "Incorrect public key length, expected {}, found {}",
                KEY_AGREEMENT_ALGORITHM_KEY_LENGTH,
                public_key.len()
            ))
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
            .context("Couldn't derive session keys")?;
        let encryptor = AeadEncryptor::new(encryption_key, decryption_key);
        Ok(encryptor)
    }

    /// Implementation of the session keys derivation.
    /// Returns a tuple with an encryption key and a decryption key.
    pub(crate) fn derive_session_keys(
        self,
        peer_public_key: &[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH],
    ) -> anyhow::Result<(EncryptionKey, DecryptionKey)> {
        let type_ = self.type_.clone();
        let self_public_key = self.public_key().context("Couldn't get self public key")?;
        let (encryption_key, decryption_key) = agreement::agree_ephemeral(
            self.private_key,
            &agreement::UnparsedPublicKey::new(KEY_AGREEMENT_ALGORITHM, peer_public_key),
            |key_material| -> Result<
                (
                    Result<[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH], anyhow::Error>,
                    Result<[u8; KEY_AGREEMENT_ALGORITHM_KEY_LENGTH], anyhow::Error>,
                ),
                anyhow::Error,
            > {
                let key_material = key_material
                    .try_into()
                    .map_err(anyhow::Error::msg)
                    .context(format!(
                        "Incorrect key material length, expected {}, found {}",
                        KEY_AGREEMENT_ALGORITHM_KEY_LENGTH,
                        key_material.len()
                    ))?;
                let peer_public_key = *peer_public_key;
                match type_ {
                    // On the server side `self_public_key` is the server key.
                    KeyNegotiatorType::Server => {
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
                    KeyNegotiatorType::Client => {
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
        .map_err(anyhow::Error::msg)
        .context("Couldn't derive session keys")?
        .context("Couldn't agree on session keys")?;
        Ok((
            EncryptionKey(encryption_key.context("Couldn't derive encryption key")?),
            DecryptionKey(decryption_key.context("Couldn't derive decryption key")?),
        ))
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
        let info = vec![key_purpose.as_bytes(), server_public_key, client_public_key];

        // Initialize key derivation function.
        let salt = Salt::new(HKDF_SHA256, KEY_DERIVATION_SALT.as_bytes());
        let kdf = salt.extract(key_material);

        // Derive session key.
        let mut session_key: [u8; AEAD_ALGORITHM_KEY_LENGTH] = Default::default();
        let output_key_material = kdf
            .expand(&info, AEAD_ALGORITHM)
            .map_err(|error| anyhow!("Couldn't run HKDF-Expand operation : {:?}", error))?;
        output_key_material
            .fill(&mut session_key)
            .map_err(|error| {
                anyhow!(
                    "Couldn't get the output of the HKDF-Expand operation: {:?}",
                    error
                )
            })?;
        Ok(session_key)
    }
}

/// Defines the type of key negotiator and the set of session keys created by it.
#[derive(Clone)]
pub enum KeyNegotiatorType {
    /// Defines a key negotiator which provides server session key for encryption and client
    /// session key for decryption.
    Server,
    /// Defines a key negotiator which provides client session key for encryption and server
    /// session key for decryption.
    Client,
}

pub struct Signer {
    /// Parsed PKCS#8 v2 key pair representation.
    key_pair: EcdsaKeyPair,
}

impl Signer {
    pub fn create() -> anyhow::Result<Self> {
        // TODO(#2557): Ensure SystemRandom work when building for x86_64 UEFI targets.
        let rng = ring::rand::SystemRandom::new();
        let key_pair_pkcs8 = EcdsaKeyPair::generate_pkcs8(SIGNING_ALGORITHM, &rng)
            .map_err(|error| anyhow!("Couldn't generate PKCS#8 key pair: {:?}", error))?;
        let key_pair =
            EcdsaKeyPair::from_pkcs8(SIGNING_ALGORITHM, key_pair_pkcs8.as_ref(), &rng)
                .map_err(|error| anyhow!("Couldn't parse generated key pair: {:?}", error))?;

        Ok(Self { key_pair })
    }

    pub fn public_key(&self) -> anyhow::Result<[u8; SIGNING_ALGORITHM_KEY_LENGTH]> {
        let public_key = self.key_pair.public_key().as_ref().to_vec();
        public_key
            .as_slice()
            .try_into()
            .map_err(anyhow::Error::msg)
            .context(format!(
                "Incorrect public key length, expected {}, found {}",
                SIGNING_ALGORITHM_KEY_LENGTH,
                public_key.len()
            ))
    }

    pub fn sign(&self, input: &[u8]) -> anyhow::Result<[u8; SIGNATURE_LENGTH]> {
        let rng = ring::rand::SystemRandom::new();
        let signature = self
            .key_pair
            .sign(&rng, input)
            .map_err(|error| anyhow!("Couldn't sign input: {:?}", error))?
            .as_ref()
            .to_vec();
        signature
            .as_slice()
            .try_into()
            .map_err(anyhow::Error::msg)
            .context(format!(
                "Incorrect signature length, expected {}, found {}",
                SIGNATURE_LENGTH,
                signature.len()
            ))
    }
}

pub struct SignatureVerifier {
    public_key_bytes: [u8; SIGNING_ALGORITHM_KEY_LENGTH],
}

impl SignatureVerifier {
    pub fn new(public_key_bytes: &[u8; SIGNING_ALGORITHM_KEY_LENGTH]) -> Self {
        Self {
            public_key_bytes: *public_key_bytes,
        }
    }

    /// Verifies the signature validity.
    pub fn verify(&self, input: &[u8], signature: &[u8; SIGNATURE_LENGTH]) -> anyhow::Result<()> {
        let public_key =
            ring::signature::UnparsedPublicKey::new(VERIFICATION_ALGORITHM, &self.public_key_bytes);
        public_key
            .verify(input, signature)
            .map_err(|error| anyhow!("Signature verification failed: {:?}", error))?;
        Ok(())
    }
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> [u8; SHA256_HASH_LENGTH] {
    digest(&SHA256, input)
        .as_ref()
        .try_into()
        .expect("Incorrect SHA-256 hash length")
}

/// Generates a random vector of `size` bytes.
pub fn get_random<const L: usize>() -> anyhow::Result<[u8; L]> {
    let mut result: [u8; L] = [Default::default(); L];
    let rng = SystemRandom::new();
    rng.fill(&mut result[..])
        .map_err(|error| anyhow!("Couldn't create random value: {:?}", error))?;
    Ok(result)
}
