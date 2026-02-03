// Copyright 2024 Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use alloc::{boxed::Box, vec::Vec};

pub use crate::noise_handshake::crypto_wrapper::{
    EcdsaKeyPair, NONCE_LEN, P256_SCALAR_LEN, P256_X962_LEN, P256Scalar, SHA256_OUTPUT_LEN,
    SYMMETRIC_KEY_LEN, aes_256_gcm_open_in_place, aes_256_gcm_seal_in_place, ecdsa_verify,
    hkdf_sha256, p256_scalar_mult, rand_bytes, sha256, sha256_two_part,
};
use crate::noise_handshake::{
    IdentityKeyHandle, NoiseMessage, OrderedCrypter,
    error::Error,
    noise::{HandshakeType, Noise},
};

pub struct HandshakeInitiator {
    noise: Noise,
    peer_identity_pub_key: Option<[u8; P256_X962_LEN]>,
    self_identity_priv_key: Option<Box<dyn IdentityKeyHandle>>,
    ephemeral_priv_key: P256Scalar,
}

impl HandshakeInitiator {
    pub fn new_nk(peer_public_key: &[u8; P256_X962_LEN]) -> Self {
        Self {
            noise: Noise::new(HandshakeType::Nk),
            peer_identity_pub_key: Some(*peer_public_key),
            self_identity_priv_key: None,
            ephemeral_priv_key: P256Scalar::generate(),
        }
    }

    pub fn new_nn() -> Self {
        Self {
            noise: Noise::new(HandshakeType::Nn),
            peer_identity_pub_key: None,
            self_identity_priv_key: None,
            ephemeral_priv_key: P256Scalar::generate(),
        }
    }
    pub fn new_kk(
        peer_public_key: [u8; P256_X962_LEN],
        self_priv_key: Box<dyn IdentityKeyHandle>,
    ) -> Self {
        Self {
            noise: Noise::new(HandshakeType::Kk),
            peer_identity_pub_key: Some(peer_public_key),
            self_identity_priv_key: Some(self_priv_key),
            ephemeral_priv_key: P256Scalar::generate(),
        }
    }

    pub fn build_initial_message(&mut self) -> Result<NoiseMessage, Error> {
        self.noise.mix_hash(&[0; 1]);
        if let Some(peer_identity_pub_key) = self.peer_identity_pub_key {
            self.noise.mix_hash_point(peer_identity_pub_key.as_slice());
        }
        let ephemeral_pub_key = self.ephemeral_priv_key.compute_public_key();
        let ephemeral_pub_key_bytes = ephemeral_pub_key.as_ref();

        self.noise.mix_hash(ephemeral_pub_key_bytes);
        self.noise.mix_key(ephemeral_pub_key_bytes);
        if let Some(peer_identity_pub_key) = self.peer_identity_pub_key {
            let es_ecdh_bytes = p256_scalar_mult(&self.ephemeral_priv_key, &peer_identity_pub_key)
                .map_err(|_| Error::InvalidHandshake)?;
            self.noise.mix_key(&es_ecdh_bytes);
        }
        if let Some(self_priv_key) = self.self_identity_priv_key.as_ref() {
            let self_static_pub_key =
                self_priv_key.get_public_key().map_err(|_| Error::InvalidPublicKey)?;
            if let Some(peer_identity_pub_key) = self.peer_identity_pub_key {
                let ss_ecdh_bytes = sha256_two_part(&self_static_pub_key, &peer_identity_pub_key);
                self.noise.mix_key(&ss_ecdh_bytes);
            } else {
                return Err(Error::MissingPeerPublicKey);
            }
        }
        if let Some(self_priv_key) = self.self_identity_priv_key.as_ref() {
            if let Some(peer_identity_pub_key) = self.peer_identity_pub_key {
                let se_ecdh_bytes = self_priv_key
                    .derive_dh_secret(peer_identity_pub_key.as_slice())
                    .map_err(|_| Error::InvalidHandshake)?;
                self.noise.mix_key(&se_ecdh_bytes);
            } else {
                return Err(Error::MissingPeerPublicKey);
            }
        }
        let ciphertext = self.noise.encrypt_and_hash(&[]);
        Ok(NoiseMessage { ciphertext, ephemeral_public_key: ephemeral_pub_key.to_vec() })
    }

    pub fn process_response(
        &mut self,
        handshake_response: &NoiseMessage,
    ) -> Result<([u8; SHA256_OUTPUT_LEN], OrderedCrypter), Error> {
        let ee_ecdh_bytes = p256_scalar_mult(
            &self.ephemeral_priv_key,
            handshake_response
                .ephemeral_public_key
                .as_slice()
                .try_into()
                .map_err(|_| Error::DecryptFailed)?,
        )
        .map_err(|_| Error::InvalidHandshake)?;
        self.noise.mix_hash(&handshake_response.ephemeral_public_key);
        self.noise.mix_key(&handshake_response.ephemeral_public_key);
        self.noise.mix_key(&ee_ecdh_bytes);
        let plaintext = self
            .noise
            .decrypt_and_hash(&handshake_response.ciphertext)
            .map_err(|_| Error::DecryptFailed)?;
        assert_eq!(plaintext.len(), 0);
        let (write_key, read_key) = self.noise.traffic_keys();
        Ok((self.noise.handshake_hash(), OrderedCrypter::new(&read_key, &write_key)))
    }
}
