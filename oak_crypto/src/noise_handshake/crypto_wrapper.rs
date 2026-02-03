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

//! The original code supported multiple back-end crypto libraries, but was
//! heavily influenced by the first: Ring.  The result was a bit hackish, and
//! should be cleaned up.

#![allow(clippy::result_unit_err)]

/// This info is always included to the caller-provided info when creating a
/// [`SessionBindingToken`], to ensure that we never just hash the unmodified
/// handshake hash in the case were a caller provides empty info.
/// Generated randomly with: `printf "%020lu\n" "0x$(openssl rand -hex 8)"`
pub const MANDATORY_SESSION_BINDING_INFO: &[u8] = b"11947944922982068094";

pub const NONCE_LEN: usize = 12;
pub const SHA256_OUTPUT_LEN: usize = 32;
pub const SYMMETRIC_KEY_LEN: usize = 32;

/// The length of an uncompressed, X9.62 encoding of a P-256 point.
pub const P256_X962_LEN: usize = 65;

/// The length of a P-256 scalar value.
pub const P256_SCALAR_LEN: usize = 32;

use alloc::vec::Vec;

use aes_gcm::{AeadInPlace, KeyInit};
use ecdsa;
use p256::ecdsa::signature::Signer;
use pkcs8::{DecodePrivateKey, EncodePrivateKey};
use primeorder::{
    Field, PrimeField,
    elliptic_curve::{
        ops::{Mul, MulByGenerator},
        sec1::{FromEncodedPoint, ToEncodedPoint},
    },
};
use rand_core::{RngCore, SeedableRng};
use sha2::Digest;

use crate::noise_handshake::crypto_wrapper::ecdsa::signature::Verifier;

pub fn rand_bytes(output: &mut [u8]) {
    let mut rng = rand_chacha::ChaCha20Rng::from_entropy();
    rng.fill_bytes(output);
}

/// Perform the HKDF operation from https://datatracker.ietf.org/doc/html/rfc5869
pub fn hkdf_sha256(ikm: &[u8], salt: &[u8], info: &[u8], output: &mut [u8]) -> Result<(), ()> {
    hkdf::Hkdf::<sha2::Sha256>::new(Some(salt), ikm).expand(info, output).map_err(|_| ())
}

pub fn aes_256_gcm_seal_in_place(
    key: &[u8; SYMMETRIC_KEY_LEN],
    nonce: &[u8; NONCE_LEN],
    aad: &[u8],
    plaintext: &mut Vec<u8>,
) {
    aes_gcm::Aes256Gcm::new_from_slice(key.as_slice())
        .unwrap()
        .encrypt_in_place(nonce.into(), aad, plaintext)
        .unwrap();
}

pub fn aes_256_gcm_open_in_place(
    key: &[u8; SYMMETRIC_KEY_LEN],
    nonce: &[u8; NONCE_LEN],
    aad: &[u8],
    mut ciphertext: Vec<u8>,
) -> Result<Vec<u8>, ()> {
    aes_gcm::Aes256Gcm::new_from_slice(key.as_slice())
        .unwrap()
        .decrypt_in_place(nonce.into(), aad, &mut ciphertext)
        .map_err(|_| ())?;
    Ok(ciphertext)
}

pub fn sha256(input: &[u8]) -> [u8; SHA256_OUTPUT_LEN] {
    let mut ctx = sha2::Sha256::new();
    ctx.update(input);
    ctx.finalize().into()
}

/// Compute the SHA-256 hash of the concatenation of two inputs.
pub fn sha256_two_part(input1: &[u8], input2: &[u8]) -> [u8; SHA256_OUTPUT_LEN] {
    let mut ctx = sha2::Sha256::new();
    ctx.update(input1);
    ctx.update(input2);
    ctx.finalize().into()
}

/// Compute a session token hash from the three provided elements.
/// A session token is a unique token that's bound to an established noise
/// session.
///
/// It's a hash computed from the provided `handshake_hash` along with a
/// caller-provided `info` string. An additional hard-coded MANDATORY_INFO
/// string is included to avoid the possiblity of hashing the handshake_hash
/// alone.
pub fn session_binding_token_hash(handshake_hash: &[u8], info: &[u8]) -> [u8; SHA256_OUTPUT_LEN] {
    let info_hash = {
        let mut ctx = sha2::Sha256::new();
        ctx.update(info);
        ctx.finalize()
    };

    let mut ctx = sha2::Sha256::new();
    ctx.update(handshake_hash);
    ctx.update(info_hash);
    ctx.update(MANDATORY_SESSION_BINDING_INFO);
    ctx.finalize().into()
}

pub struct P256Scalar {
    v: p256::Scalar,
}

impl P256Scalar {
    pub fn generate() -> P256Scalar {
        let mut ret = [0u8; P256_SCALAR_LEN];
        rand_bytes(&mut ret);
        P256Scalar::from_bytes(ret)
    }

    pub fn from_bytes(bytes: [u8; P256_SCALAR_LEN]) -> P256Scalar {
        P256Scalar { v: p256::Scalar::from_repr(bytes.into()).unwrap() }
    }

    pub fn compute_public_key(&self) -> [u8; P256_X962_LEN] {
        p256::ProjectivePoint::mul_by_generator(&self.v)
            .to_encoded_point(false)
            .as_bytes()
            .try_into()
            .unwrap()
    }

    pub fn bytes(&self) -> [u8; P256_SCALAR_LEN] {
        self.v.to_repr().as_slice().try_into().unwrap()
    }
}

impl TryFrom<&[u8]> for P256Scalar {
    type Error = ();

    fn try_from(bytes: &[u8]) -> Result<Self, ()> {
        let array: [u8; P256_SCALAR_LEN] = bytes.try_into().map_err(|_| ())?;
        (&array).try_into()
    }
}

impl TryFrom<&[u8; P256_SCALAR_LEN]> for P256Scalar {
    type Error = ();

    fn try_from(bytes: &[u8; P256_SCALAR_LEN]) -> Result<Self, ()> {
        let scalar = p256::Scalar::from_repr((*bytes).into());
        if !bool::from(scalar.is_some()) {
            return Err(());
        }
        let scalar = scalar.unwrap();
        if scalar.is_zero_vartime() {
            return Err(());
        }
        Ok(P256Scalar { v: scalar })
    }
}

pub fn p256_scalar_mult(
    scalar: &P256Scalar,
    point: &[u8; P256_X962_LEN],
) -> Result<[u8; P256_SCALAR_LEN], ()> {
    let point = p256::EncodedPoint::from_bytes(point).map_err(|_| ())?;
    let affine_point = p256::AffinePoint::from_encoded_point(&point);
    if !bool::from(affine_point.is_some()) {
        // The peer's point is considered public input and so we don't need to work in
        // constant time.
        return Err(());
    }
    // unwrap: `is_some` checked just above.
    let result = affine_point.unwrap().mul(scalar.v).to_encoded_point(false);
    let x = result.x().ok_or(())?;
    // unwrap: the length of a P256 field-element had better be 32 bytes.
    Ok(x.as_slice().try_into().unwrap())
}

pub struct EcdsaKeyPair {
    key_pair: p256::ecdsa::SigningKey,
}

impl EcdsaKeyPair {
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<EcdsaKeyPair, ()> {
        let key_pair: p256::ecdsa::SigningKey =
            p256::ecdsa::SigningKey::from_pkcs8_der(pkcs8).map_err(|_| ())?;
        Ok(EcdsaKeyPair { key_pair })
    }

    pub fn generate_pkcs8() -> Result<impl AsRef<[u8]>, ()> {
        // WARNING: not actually a random scalar
        let mut scalar = [0u8; P256_SCALAR_LEN];
        scalar[0] = 42;
        let non_zero_scalar = p256::NonZeroScalar::from_repr(scalar.into()).unwrap();
        let key = p256::ecdsa::SigningKey::from(non_zero_scalar);
        Ok(key.to_pkcs8_der().map_err(|_| ())?.to_bytes())
    }

    pub fn public_key(&self) -> impl AsRef<[u8]> + '_ {
        p256::ecdsa::VerifyingKey::from(&self.key_pair).to_sec1_bytes()
    }

    pub fn sign(&self, signed_data: &[u8]) -> Result<impl AsRef<[u8]>, ()> {
        let sig: ecdsa::Signature<p256::NistP256> = self.key_pair.sign(signed_data);
        Ok(sig.to_der())
    }
}

#[must_use]
pub fn ecdsa_verify(pub_key: &[u8], signed_data: &[u8], signature: &[u8]) -> bool {
    let signature = match ecdsa::der::Signature::from_bytes(signature) {
        Ok(signature) => signature,
        Err(_) => return false,
    };
    let key = match p256::ecdsa::VerifyingKey::from_sec1_bytes(pub_key) {
        Ok(key) => key,
        Err(_) => return false,
    };
    key.verify(signed_data, &signature).is_ok()
}
