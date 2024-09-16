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

//! This was copied from Chromium's third_party/cloud_authenticator, which has
//! compatible copyright and ownership (Apache 2.0, Google).

#[allow(unused_imports)] // Macros only used in tests.
#[macro_use]

pub mod client;
mod crypto_wrapper;
mod error;
mod noise;
#[cfg(test)]
mod tests;
use alloc::vec::Vec;

use anyhow::anyhow;
use oak_proto_rust::oak::{crypto::v1::SessionKeys, session::v1::NoiseHandshakeMessage};

use crate::noise_handshake::{
    error::Error,
    noise::{HandshakeType, Noise},
};
pub use crate::{
    identity_key::IdentityKeyHandle,
    noise_handshake::crypto_wrapper::{
        aes_256_gcm_open_in_place, aes_256_gcm_seal_in_place, ecdsa_verify, hkdf_sha256,
        p256_scalar_mult, rand_bytes, sha256, sha256_two_part, EcdsaKeyPair, P256Scalar, NONCE_LEN,
        P256_X962_LEN, SHA256_OUTPUT_LEN, SYMMETRIC_KEY_LEN,
    },
};

// This is assumed to be vastly larger than any connection will ever reach.
const MAX_SEQUENCE: u32 = 1u32 << 24;

pub struct Nonce {
    pub nonce: u32,
}

impl Nonce {
    pub fn next(&mut self) -> Result<[u8; NONCE_LEN], Error> {
        if self.nonce > MAX_SEQUENCE {
            return Err(Error::DecryptFailed);
        }
        let mut ret = [0u8; NONCE_LEN];
        ret[NONCE_LEN - 4..].copy_from_slice(self.nonce.to_be_bytes().as_slice());
        self.nonce += 1;
        Ok(ret)
    }
}

pub struct NoiseMessage {
    pub ephemeral_public_key: Vec<u8>,
    pub ciphertext: Vec<u8>,
}

impl From<&NoiseHandshakeMessage> for NoiseMessage {
    fn from(value: &NoiseHandshakeMessage) -> Self {
        NoiseMessage {
            ephemeral_public_key: value.ephemeral_public_key.clone(),
            ciphertext: value.ciphertext.clone(),
        }
    }
}

pub struct Crypter {
    read_key: [u8; SYMMETRIC_KEY_LEN],
    write_key: [u8; SYMMETRIC_KEY_LEN],
    read_nonce: Nonce,
    write_nonce: Nonce,
}

/// Utility for encrypting and decrypting traffic between the Noise endpoints.
/// It is created by |respond| and configured with a key for each traffic
/// direction.
impl Crypter {
    fn new(read_key: &[u8; SYMMETRIC_KEY_LEN], write_key: &[u8; SYMMETRIC_KEY_LEN]) -> Self {
        Self {
            read_key: *read_key,
            write_key: *write_key,
            read_nonce: Nonce { nonce: 0 },
            write_nonce: Nonce { nonce: 0 },
        }
    }

    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>, Error> {
        const PADDING_GRANULARITY: usize = 32;
        static_assertions::const_assert!(PADDING_GRANULARITY < 256);
        static_assertions::const_assert!((PADDING_GRANULARITY & (PADDING_GRANULARITY - 1)) == 0);

        let mut padded_size: usize = plaintext.len();
        // AES GCM is limited to encrypting 64GiB of data with the same key.
        // TODO(#4917): in a follow-on CL, track total data per key and drop the
        // connection after 64 GiB. 256MiB is just a sane upper limit on
        // message size, which greatly exceeds the noise specified 64KiB, which
        // will be too restrictive for our use cases.
        if padded_size > (1usize << 28) {
            return Err(Error::DataTooLarge(padded_size));
        }
        padded_size += 1; // padding-length byte
        // This is standard low-level bit manipulation to round up to the nearest
        // multiple of PADDING_GRANULARITY.  We know PADDING_GRANULARRITY is a
        // power of 2, so we compute the mask with !(PADDING_GRANULARITY - 1).
        // If padded_size is not already a multiple of PADDING_GRANULARITY, then
        // padded_size will not change.  Otherwise, it is rounded up to the next
        // multiple of PADDED_GRANULARITY.
        padded_size = (padded_size + PADDING_GRANULARITY - 1) & !(PADDING_GRANULARITY - 1);

        let mut padded_encrypt_data = Vec::with_capacity(padded_size);
        padded_encrypt_data.extend_from_slice(plaintext);
        padded_encrypt_data.resize(padded_size, 0u8);
        let num_zeros = padded_size - plaintext.len() - 1;
        padded_encrypt_data[padded_size - 1] = num_zeros as u8;

        crypto_wrapper::aes_256_gcm_seal_in_place(
            &self.write_key,
            &self.write_nonce.next()?,
            &[],
            &mut padded_encrypt_data,
        );
        Ok(padded_encrypt_data)
    }

    pub fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
        let plaintext = crypto_wrapper::aes_256_gcm_open_in_place(
            &self.read_key,
            &self.read_nonce.next()?,
            &[],
            Vec::from(ciphertext),
        )
        .map_err(|_| Error::DecryptFailed)?;

        // Plaintext must have a padding byte, and the unpadded length must be
        // at least one.
        if plaintext.is_empty() || (plaintext[plaintext.len() - 1] as usize) >= plaintext.len() {
            return Err(Error::DecryptionPadding);
        }
        let unpadded_length = plaintext.len() - (plaintext[plaintext.len() - 1] as usize);
        Ok(Vec::from(&plaintext[0..unpadded_length - 1]))
    }
}

impl From<Crypter> for SessionKeys {
    fn from(value: Crypter) -> Self {
        SessionKeys { request_key: value.write_key.to_vec(), response_key: value.read_key.to_vec() }
    }
}

impl TryFrom<SessionKeys> for Crypter {
    type Error = anyhow::Error;

    fn try_from(sk: SessionKeys) -> Result<Self, Self::Error> {
        Ok(Crypter::new(
            sk.response_key
                .as_slice()
                .try_into()
                .map_err(|e| anyhow!("unexpected format of the read key: {e:#?}"))?,
            sk.request_key
                .as_slice()
                .try_into()
                .map_err(|e| anyhow!("unexpected format of the read key: {e:#?}"))?,
        ))
    }
}

pub struct Response {
    pub crypter: Crypter,
    pub handshake_hash: [u8; SHA256_OUTPUT_LEN],
    pub response: NoiseMessage,
}

pub fn respond_nk(
    identity_key: &dyn IdentityKeyHandle,
    in_message: &NoiseMessage,
) -> Result<Response, Error> {
    let mut noise = Noise::new(HandshakeType::Nk);
    noise.mix_hash(&[0; 1]); // Prologue
    noise.mix_hash_point(
        identity_key.get_public_key().map_err(|_| Error::InvalidPrivateKey)?.as_slice(),
    );

    // unwrap: we know that `in_data` is `P256_X962_LENGTH` bytes long.
    noise.mix_hash(in_message.ephemeral_public_key.as_slice());
    noise.mix_key(in_message.ephemeral_public_key.as_slice());

    let es_ecdh_bytes = identity_key
        .derive_dh_secret(in_message.ephemeral_public_key.as_slice())
        .map_err(|_| Error::InvalidHandshake)?;
    noise.mix_key(es_ecdh_bytes.as_slice());
    finish_response(&mut noise, in_message)
}

pub fn respond_nn(in_message: &NoiseMessage) -> Result<Response, Error> {
    let mut noise = Noise::new(HandshakeType::Nn);
    noise.mix_hash(&[0; 1]); // Prologue

    noise.mix_hash(in_message.ephemeral_public_key.as_slice());
    noise.mix_key(&in_message.ephemeral_public_key.as_slice());
    finish_response(&mut noise, in_message)
}

pub fn respond_kk(
    // responder e
    identity_priv: &dyn IdentityKeyHandle,
    // initiator s [not used for Nk]
    initiator_static_pub: &[u8],
    // e, es, (ss for Kk only)
    in_message: &NoiseMessage,
) -> Result<Response, Error> {
    let mut noise = Noise::new(HandshakeType::Kk);
    noise.mix_hash(&[0; 1]); // Prologue
    noise.mix_hash_point(
        identity_priv.get_public_key().map_err(|_| Error::InvalidPrivateKey)?.as_slice(),
    );

    noise.mix_hash(in_message.ephemeral_public_key.as_slice());
    noise.mix_key(in_message.ephemeral_public_key.as_slice());

    let es_ecdh_bytes = identity_priv
        .derive_dh_secret(in_message.ephemeral_public_key.as_slice())
        .map_err(|_| Error::InvalidHandshake)?;
    noise.mix_key(es_ecdh_bytes.as_slice());

    let initiator_static_pub_bytes: [u8; P256_X962_LEN] =
        initiator_static_pub.try_into().map_err(|_| Error::InvalidPublicKey)?;

    let ss_ecdh_bytes =
        sha256_two_part(&initiator_static_pub_bytes, &identity_priv.get_public_key().unwrap());
    noise.mix_key(&ss_ecdh_bytes);

    let se_ecdh_bytes = identity_priv
        .derive_dh_secret(initiator_static_pub_bytes.as_slice())
        .map_err(|_| Error::InvalidHandshake)?;
    noise.mix_key(&se_ecdh_bytes);
    finish_response(&mut noise, in_message)
}

fn finish_response(noise: &mut Noise, in_message: &NoiseMessage) -> Result<Response, Error> {
    let plaintext = noise.decrypt_and_hash(&in_message.ciphertext)?;
    if !plaintext.is_empty() {
        return Err(Error::InvalidHandshake);
    }

    // Generate ephemeral key pair
    let ephemeral_priv = P256Scalar::generate();
    let ephemeral_pub_key_bytes = ephemeral_priv.compute_public_key();
    noise.mix_hash(ephemeral_pub_key_bytes.as_slice());
    noise.mix_key(ephemeral_pub_key_bytes.as_slice());
    let ee_ecdh_bytes = crypto_wrapper::p256_scalar_mult(
        &ephemeral_priv,
        in_message
            .ephemeral_public_key
            .as_slice()
            .try_into()
            .map_err(|_| Error::InvalidPublicKey)?,
    )
    .map_err(|_| Error::InvalidHandshake)?;
    noise.mix_key(ee_ecdh_bytes.as_slice());

    let response_ciphertext = noise.encrypt_and_hash(&[]);

    let keys = noise.traffic_keys();
    Ok(Response {
        crypter: Crypter::new(&keys.0, &keys.1),
        handshake_hash: noise.handshake_hash(),
        response: NoiseMessage {
            ciphertext: response_ciphertext,
            ephemeral_public_key: ephemeral_pub_key_bytes.to_vec(),
        },
    })
}
