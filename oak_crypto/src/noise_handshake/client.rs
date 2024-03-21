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

use alloc::vec::Vec;

pub use crate::noise_handshake::crypto_wrapper::{
    aes_256_gcm_open_in_place, aes_256_gcm_seal_in_place, ecdsa_verify, hkdf_sha256,
    p256_scalar_mult, rand_bytes, sha256, sha256_two_part, EcdsaKeyPair, P256Scalar, NONCE_LEN,
    P256_X962_LEN, SHA256_OUTPUT_LEN, SYMMETRIC_KEY_LEN,
};
use crate::noise_handshake::{
    error::Error,
    noise::{HandshakeType, Noise},
    Crypter,
};

pub struct HandshakeInitiator {
    noise: Noise,
    identity_pub_key: [u8; P256_X962_LEN],
    ephemeral_priv_key: P256Scalar,
}

impl HandshakeInitiator {
    pub fn new(peer_public_key: &[u8; P256_X962_LEN]) -> Self {
        Self {
            noise: Noise::new(HandshakeType::Nk),
            identity_pub_key: *peer_public_key,
            ephemeral_priv_key: P256Scalar::generate(),
        }
    }

    pub fn build_initial_message(&mut self) -> Vec<u8> {
        self.noise.mix_hash(&[0; 1]);
        self.noise.mix_hash_point(self.identity_pub_key.as_slice());
        let ephemeral_pub_key = self.ephemeral_priv_key.compute_public_key();
        let ephemeral_pub_key_bytes = ephemeral_pub_key.as_ref();

        self.noise.mix_hash(ephemeral_pub_key_bytes);
        self.noise.mix_key(ephemeral_pub_key_bytes);
        let es_ecdh_bytes =
            p256_scalar_mult(&self.ephemeral_priv_key, &self.identity_pub_key).unwrap();
        self.noise.mix_key(&es_ecdh_bytes);

        let ciphertext = self.noise.encrypt_and_hash(&[]);
        [ephemeral_pub_key_bytes, &ciphertext].concat()
    }

    pub fn process_response(
        &mut self,
        handshake_response: &[u8],
    ) -> ([u8; SHA256_OUTPUT_LEN], Crypter) {
        let peer_public_key_bytes = &handshake_response[..P256_X962_LEN];
        let ciphertext = &handshake_response[P256_X962_LEN..];

        let ee_ecdh_bytes =
            p256_scalar_mult(&self.ephemeral_priv_key, peer_public_key_bytes.try_into().unwrap())
                .unwrap();
        self.noise.mix_hash(peer_public_key_bytes);
        self.noise.mix_key(peer_public_key_bytes);
        self.noise.mix_key(&ee_ecdh_bytes);

        let plaintext = self.noise.decrypt_and_hash(ciphertext).unwrap();
        assert_eq!(plaintext.len(), 0);
        let (write_key, read_key) = self.noise.traffic_keys();
        (self.noise.handshake_hash(), Crypter::new(&read_key, &write_key))
    }
}
