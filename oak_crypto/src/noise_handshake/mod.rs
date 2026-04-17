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
use hashbrown::HashSet;
use oak_proto_rust::oak::session::v1::NoiseHandshakeMessage;
use zeroize::Zeroizing;

use crate::noise_handshake::{
    error::Error,
    noise::{HandshakeType, Noise},
};
pub use crate::{
    identity_key::IdentityKeyHandle,
    noise_handshake::crypto_wrapper::{
        EcdsaKeyPair, NONCE_LEN, P256_X962_LEN, P256Scalar, SHA256_OUTPUT_LEN, SYMMETRIC_KEY_LEN,
        aes_256_gcm_open_in_place, aes_256_gcm_seal_in_place, ecdsa_verify, hkdf_sha256,
        p256_scalar_mult, rand_bytes, session_binding_token_hash, sha256, sha256_two_part,
    },
};

// This is assumed to be vastly larger than any connection will ever reach.
const MAX_SEQUENCE: u32 = 1u32 << 24;

pub struct Nonce {
    pub nonce: u32,
}

impl Nonce {
    pub fn next_nonce(&mut self) -> Result<[u8; NONCE_LEN], Error> {
        if self.nonce > MAX_SEQUENCE {
            return Err(Error::DecryptFailed);
        }
        let mut ret = [0u8; NONCE_LEN];
        ret[NONCE_LEN - 4..].copy_from_slice(self.nonce.to_be_bytes().as_slice());
        self.nonce += 1;
        Ok(ret)
    }

    // Nonce must be `NONCE_LEN` bytes with the last 4 bytes holding the nonce value
    // and the rest padded with 0.
    pub fn get_nonce_value(nonce: &[u8; NONCE_LEN]) -> Result<u32, Error> {
        if !nonce.starts_with(&[0u8; NONCE_LEN - 4]) {
            return Err(Error::InvalidNonce);
        }
        let mut nonce_be_bytes = [0u8; 4];
        nonce_be_bytes.copy_from_slice(&nonce[NONCE_LEN - 4..]);
        Ok(u32::from_be_bytes(nonce_be_bytes))
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

impl From<NoiseHandshakeMessage> for NoiseMessage {
    fn from(value: NoiseHandshakeMessage) -> Self {
        NoiseMessage {
            ephemeral_public_key: value.ephemeral_public_key,
            ciphertext: value.ciphertext,
        }
    }
}

fn aes_gcm_256_encrypt(
    key: &[u8; SYMMETRIC_KEY_LEN],
    nonce: &[u8; NONCE_LEN],
    plaintext: &[u8],
) -> Result<Vec<u8>, Error> {
    // The crypto library will include a small tag at the end after encrypting.
    // We can avoid potential re-alloc in the crypto library by ensuring that
    // there's enough space for the tag when we allocate the buffer here.
    const ADDITIONAL_TAG_SPACE: usize = 32;

    const PADDING_GRANULARITY: usize = 32;
    static_assertions::const_assert!(PADDING_GRANULARITY < 256);
    static_assertions::const_assert!((PADDING_GRANULARITY & (PADDING_GRANULARITY - 1)) == 0);

    let mut padded_size: usize = plaintext.len();
    // AES GCM is limited to encrypting 64GiB of data in a single AEAD invocation.
    // 256MiB is just a sane upper limit on message size, which greatly exceeds
    // the noise specified 64KiB, which will be too restrictive for our use cases.
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

    let mut padded_encrypt_data = Vec::with_capacity(padded_size + ADDITIONAL_TAG_SPACE);
    padded_encrypt_data.extend_from_slice(plaintext);
    padded_encrypt_data.resize(padded_size, 0u8);
    let num_zeros = padded_size - plaintext.len() - 1;
    padded_encrypt_data[padded_size - 1] = num_zeros as u8;

    crypto_wrapper::aes_256_gcm_seal_in_place(key, nonce, &[], &mut padded_encrypt_data);
    Ok(padded_encrypt_data)
}

fn aes_gcm_256_decrypt(
    key: &[u8; SYMMETRIC_KEY_LEN],
    nonce: &[u8; NONCE_LEN],
    ciphertext: &[u8],
) -> Result<Vec<u8>, Error> {
    // Aes256Gcm implements Aead in terms of AeadInPlace, so even if you remove the
    // `Vec::from` here the underlying libraries will end up doing the copy anyway.
    let mut plaintext =
        crypto_wrapper::aes_256_gcm_open_in_place(key, nonce, &[], Vec::from(ciphertext))
            .map_err(|_| Error::DecryptFailed)?;

    // Plaintext must have a padding byte, and the unpadded length must be
    // at least one.
    if plaintext.is_empty() || (plaintext[plaintext.len() - 1] as usize) >= plaintext.len() {
        return Err(Error::DecryptionPadding);
    }
    let unpadded_length = plaintext.len() - (plaintext[plaintext.len() - 1] as usize);
    plaintext.truncate(unpadded_length - 1);
    Ok(plaintext)
}

pub struct OrderedCrypter {
    read_key: Zeroizing<[u8; SYMMETRIC_KEY_LEN]>,
    write_key: Zeroizing<[u8; SYMMETRIC_KEY_LEN]>,
    read_nonce: Nonce,
    write_nonce: Nonce,
}

/// Utility for encrypting and decrypting traffic between the Noise endpoints.
///
/// This implementation guarantees message ordering.
/// It is created by |respond| and configured with a key for each traffic
/// direction.
impl OrderedCrypter {
    pub fn new(read_key: &[u8; SYMMETRIC_KEY_LEN], write_key: &[u8; SYMMETRIC_KEY_LEN]) -> Self {
        Self {
            read_key: (*read_key).into(),
            write_key: (*write_key).into(),
            read_nonce: Nonce { nonce: 0 },
            write_nonce: Nonce { nonce: 0 },
        }
    }

    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>, Error> {
        aes_gcm_256_encrypt(&self.write_key, &self.write_nonce.next_nonce()?, plaintext)
    }

    pub fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
        aes_gcm_256_decrypt(&self.read_key, &self.read_nonce.next_nonce()?, ciphertext)
    }
}

/// Modified impl of `OrderedCrypter` that explicitly ignores ordering.
///
/// It explicitly ignores message ordering but protects against replayed
/// messages. This implementation ratchets messages upto a given `window_size`
/// i.e. very old messages outside the given window will fail decryption.
/// Messages within the allowed window will be decrypted in any order.
/// Applications using this implementation must ensure they can handle
/// re-ordered and dropped messages. This implementation is primarily meant for
/// unreliable transport protocols such as UDP.
pub struct UnorderedCrypter {
    read_key: Zeroizing<[u8; SYMMETRIC_KEY_LEN]>,
    write_key: Zeroizing<[u8; SYMMETRIC_KEY_LEN]>,
    write_nonce: Nonce,
    // The current furthest read nonce seen so far.
    furthest_read_nonce: u32,
    // Window size to ratchet receiving nonces in order to avoid receiving
    // nonces way too far in the past.
    window_size: u32,
    // Buffered read nonces with max capacity equivalent to `window_size` i.e.
    // nonces lower than (`furthest_read_nonce` - `window_size`) will not be decrypted.
    buffered_read_nonces: HashSet<u32>,
}

impl UnorderedCrypter {
    pub fn new(
        read_key: &[u8; SYMMETRIC_KEY_LEN],
        write_key: &[u8; SYMMETRIC_KEY_LEN],
        window_size: u32,
    ) -> Self {
        Self {
            read_key: (*read_key).into(),
            write_key: (*write_key).into(),
            write_nonce: Nonce { nonce: 1 },
            furthest_read_nonce: 0,
            window_size,
            buffered_read_nonces: HashSet::with_capacity(window_size.try_into().unwrap()),
        }
    }

    fn get_lowest_acceptable_read_nonce(&self) -> u32 {
        let mut lowest_acceptable_read_nonce = 1;
        if self.furthest_read_nonce > self.window_size {
            lowest_acceptable_read_nonce = self.furthest_read_nonce - self.window_size + 1;
        }
        lowest_acceptable_read_nonce
    }

    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let nonce = self.write_nonce.next_nonce()?;
        let encrypted_message = aes_gcm_256_encrypt(&self.write_key, &nonce, plaintext)?;
        Ok((encrypted_message, nonce.to_vec()))
    }

    pub fn decrypt(
        &mut self,
        nonce: &[u8; NONCE_LEN],
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, Error> {
        let nonce_value = Nonce::get_nonce_value(nonce)?;
        let lowest_acceptable_nonce = self.get_lowest_acceptable_read_nonce();
        // Nonce is way too far in the past, reject it.
        if nonce_value < lowest_acceptable_nonce {
            return Err(Error::InvalidNonce);
        }
        // Nonce is within the window, check for replayed nonces.
        else if nonce_value >= lowest_acceptable_nonce && nonce_value <= self.furthest_read_nonce
        {
            if self.buffered_read_nonces.contains(&nonce_value) {
                return Err(Error::ReplayedNonce);
            }
            self.buffered_read_nonces.insert(nonce_value);
        }
        // Nonce is greater than the furthest seen so far.
        else {
            self.furthest_read_nonce = nonce_value;
            // Retain only buffered nonces in the new window span.
            let new_lowest_acceptable_nonce = self.get_lowest_acceptable_read_nonce();
            self.buffered_read_nonces.retain(|&n| n >= new_lowest_acceptable_nonce);
            self.buffered_read_nonces.insert(nonce_value);
        }
        aes_gcm_256_decrypt(&self.read_key, nonce, ciphertext)
    }
}

impl TryFrom<(OrderedCrypter, u32)> for UnorderedCrypter {
    type Error = anyhow::Error;

    fn try_from(crypter_and_window_size: (OrderedCrypter, u32)) -> Result<Self, Self::Error> {
        Ok(UnorderedCrypter::new(
            &crypter_and_window_size
                .0
                .read_key
                .as_slice()
                .try_into()
                .map_err(|e| anyhow!("unexpected format of the read key: {e:#?}"))?,
            crypter_and_window_size
                .0
                .write_key
                .as_slice()
                .try_into()
                .map_err(|e| anyhow!("unexpected format of the write key: {e:#?}"))?,
            crypter_and_window_size.1,
        ))
    }
}

pub struct Response {
    pub crypter: OrderedCrypter,
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
    noise.mix_key(in_message.ephemeral_public_key.as_slice());
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
        crypter: OrderedCrypter::new(&keys.0, &keys.1),
        handshake_hash: noise.handshake_hash(),
        response: NoiseMessage {
            ciphertext: response_ciphertext,
            ephemeral_public_key: ephemeral_pub_key_bytes.to_vec(),
        },
    })
}
