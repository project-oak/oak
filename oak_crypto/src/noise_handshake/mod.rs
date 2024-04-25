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

pub use crate::noise_handshake::crypto_wrapper::{
    aes_256_gcm_open_in_place, aes_256_gcm_seal_in_place, ecdsa_verify, hkdf_sha256,
    p256_scalar_mult, rand_bytes, sha256, sha256_two_part, EcdsaKeyPair, P256Scalar, NONCE_LEN,
    P256_X962_LEN, SHA256_OUTPUT_LEN, SYMMETRIC_KEY_LEN,
};
use crate::noise_handshake::{
    error::Error,
    noise::{HandshakeType, Noise},
};

// This is assumed to be vastly larger than any connection will ever reach.
const MAX_SEQUENCE: u32 = 1u32 << 24;

pub struct Nonce {
    nonce: u32,
}

impl Nonce {
    fn next(&mut self) -> Result<[u8; NONCE_LEN], Error> {
        if self.nonce > MAX_SEQUENCE {
            return Err(Error::DecryptFailed);
        }
        let mut ret = [0u8; NONCE_LEN];
        ret[NONCE_LEN - 4..].copy_from_slice(self.nonce.to_be_bytes().as_slice());
        self.nonce += 1;
        Ok(ret)
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

pub struct Response {
    pub crypter: Crypter,
    pub handshake_hash: [u8; SHA256_OUTPUT_LEN],
    pub response: Vec<u8>,
}

/// Performs the Responder side of the Noise protocol with the NK or NN pattern.
/// |identity_private_key_bytes| contains the private key scalar for the
/// service's provisioned identity. |in_data| is provided by the Initiator and
/// contains its ephemeral public key and encrypted payload.
///
/// The identity public key is computed from the private key, but could
/// alternatively be stored separately to reduce computation if needed to
/// reduce per-transaction computation.
/// See https://noiseexplorer.com/patterns/NK/
pub fn respond_nk(identity_private_key_bytes: &[u8], in_data: &[u8]) -> Result<Response, Error> {
    if in_data.len() < P256_X962_LEN {
        return Err(Error::InvalidHandshake);
    }

    let mut noise = Noise::new(HandshakeType::Nk);
    noise.mix_hash(&[0; 1]); // Prologue

    // unwrap: we know that `in_data` is `P256_X962_LENGTH` bytes long.
    let identity_scalar: P256Scalar =
        identity_private_key_bytes.try_into().map_err(|_| Error::InvalidPrivateKey)?;
    let identity_pub = identity_scalar.compute_public_key();
    noise.mix_hash_point(identity_pub.as_slice());

    // unwrap: we know that `in_data` is `P256_X962_LENGTH` bytes long.
    let peer_pub: [u8; P256_X962_LEN] = (&in_data[..P256_X962_LEN]).try_into().unwrap();
    noise.mix_hash(peer_pub.as_slice());
    noise.mix_key(peer_pub.as_slice());

    let es_ecdh_bytes = crypto_wrapper::p256_scalar_mult(&identity_scalar, &peer_pub)
        .map_err(|_| Error::InvalidHandshake)?;
    noise.mix_key(es_ecdh_bytes.as_slice());
    finish_response(&mut noise, in_data, &peer_pub)
}

pub fn respond_nn(in_data: &[u8]) -> Result<Response, Error> {
    if in_data.len() < P256_X962_LEN {
        return Err(Error::InvalidHandshake);
    }

    let mut noise = Noise::new(HandshakeType::Nn);
    noise.mix_hash(&[0; 1]); // Prologue

    // unwrap: we know that `in_data` is `P256_X962_LENGTH` bytes long.
    let peer_pub: [u8; P256_X962_LEN] = (&in_data[..P256_X962_LEN]).try_into().unwrap();
    noise.mix_hash(peer_pub.as_slice());
    noise.mix_key(peer_pub.as_slice());
    finish_response(&mut noise, in_data, &peer_pub)
}

fn finish_response(
    noise: &mut Noise,
    in_data: &[u8],
    peer_pub: &[u8; P256_X962_LEN],
) -> Result<Response, Error> {
    let plaintext = noise.decrypt_and_hash(&in_data[P256_X962_LEN..])?;
    if !plaintext.is_empty() {
        return Err(Error::InvalidHandshake);
    }

    // Generate ephemeral key pair
    let ephemeral_priv = P256Scalar::generate();
    let ephemeral_pub_key_bytes = ephemeral_priv.compute_public_key();
    noise.mix_hash(ephemeral_pub_key_bytes.as_slice());
    noise.mix_key(ephemeral_pub_key_bytes.as_slice());
    let ee_ecdh_bytes = crypto_wrapper::p256_scalar_mult(&ephemeral_priv, peer_pub)
        .map_err(|_| Error::InvalidHandshake)?;
    noise.mix_key(ee_ecdh_bytes.as_slice());

    let response_ciphertext = noise.encrypt_and_hash(&[]);

    let keys = noise.traffic_keys();
    Ok(Response {
        crypter: Crypter::new(&keys.0, &keys.1),
        handshake_hash: noise.handshake_hash(),
        response: [ephemeral_pub_key_bytes.as_slice(), &response_ciphertext].concat(),
    })
}
