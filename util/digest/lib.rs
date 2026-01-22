//
// Copyright 2025 The Project Oak Authors
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

//! Provides native Rust structs around digests and related conversion:
//!
//!   Digest:
//!       An enum capturing the result of common hashing algorithms.
//!
//! The protocol buffers RawDigest, HexDigest used in APIs can be converted
//! from Digest, but not to it, unless the digest type that should be kept
//! is specified.

#![no_std]

extern crate alloc;
use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

use oak_proto_rust::oak::{HexDigest, RawDigest};
use sha2::{
    Digest as Sha2DigestTrait, Sha256 as Sha256Hasher, Sha384 as Sha384Hasher,
    Sha512 as Sha512Hasher,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DigestError {
    #[error("mismatched digests: expected={expected:?} actual={actual:?}")]
    CompareMismatch { expected: String, actual: String },
    #[error("undecidable")]
    CompareUndecidable,
    #[error("hash collision")]
    CompareContradiction,
    #[error("invalid digest spec")]
    InvalidDigestSpec,
    #[error("duplicate key {0}")]
    DuplicateKey(String),
    #[error("unknown digest key {0}")]
    UnknownKey(String),
    #[error("could not decode field {name}: {value}")]
    HexDecodingError {
        name: String,
        value: String,
        #[source]
        source: hex::FromHexError,
    },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Psha2(Vec<u8>);

impl Psha2 {
    pub fn from_contents(_input: &[u8]) -> Self {
        todo!("unimplemented")
    }

    pub fn to_typed_hash(&self) -> String {
        format!("psha2:{}", hex::encode(&self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha1([u8; 20]);

impl Sha1 {
    pub fn to_typed_hash(&self) -> String {
        format!("sha1:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha256([u8; 32]);

impl Sha256 {
    pub fn from_contents(input: &[u8]) -> Self {
        let mut hasher = Sha256Hasher::new();
        hasher.update(input);
        Self(hasher.finalize().into())
    }

    pub fn to_typed_hash(&self) -> String {
        format!("sha256:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha384([u8; 48]);

impl Sha384 {
    pub fn from_contents(input: &[u8]) -> Self {
        let mut hasher = Sha384Hasher::new();
        hasher.update(input);
        Self(hasher.finalize().into())
    }

    pub fn to_typed_hash(&self) -> String {
        format!("sha384:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha512([u8; 64]);

impl Sha512 {
    pub fn from_contents(input: &[u8]) -> Self {
        let mut hasher = Sha512Hasher::new();
        hasher.update(input);
        Self(hasher.finalize().into())
    }

    pub fn to_typed_hash(&self) -> String {
        format!("sha512:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_224([u8; 28]);

impl Sha3_224 {
    pub fn to_typed_hash(&self) -> String {
        format!("sha3_224:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_256([u8; 32]);

impl Sha3_256 {
    pub fn to_typed_hash(&self) -> String {
        format!("sha3_256:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_384([u8; 48]);

impl Sha3_384 {
    pub fn to_typed_hash(&self) -> String {
        format!("sha3_384:{}", hex::encode(self.0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_512([u8; 64]);

impl Sha3_512 {
    pub fn to_typed_hash(&self) -> String {
        format!("sha3_512:{}", hex::encode(self.0))
    }
}

impl From<Vec<u8>> for Psha2 {
    fn from(v: Vec<u8>) -> Self {
        Self(v)
    }
}
impl From<[u8; 20]> for Sha1 {
    fn from(v: [u8; 20]) -> Self {
        Self(v)
    }
}
impl From<[u8; 32]> for Sha256 {
    fn from(v: [u8; 32]) -> Self {
        Self(v)
    }
}
impl From<[u8; 48]> for Sha384 {
    fn from(v: [u8; 48]) -> Self {
        Self(v)
    }
}
impl From<[u8; 64]> for Sha512 {
    fn from(v: [u8; 64]) -> Self {
        Self(v)
    }
}
impl From<[u8; 28]> for Sha3_224 {
    fn from(v: [u8; 28]) -> Self {
        Self(v)
    }
}
impl From<[u8; 32]> for Sha3_256 {
    fn from(v: [u8; 32]) -> Self {
        Self(v)
    }
}
impl From<[u8; 48]> for Sha3_384 {
    fn from(v: [u8; 48]) -> Self {
        Self(v)
    }
}
impl From<[u8; 64]> for Sha3_512 {
    fn from(v: [u8; 64]) -> Self {
        Self(v)
    }
}

impl AsRef<[u8]> for Sha1 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha256 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha384 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha512 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_224 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_256 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_384 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_512 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Psha2 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Represents a specific digest type and its (mostly) fixed-size data.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Digest {
    Sha1(Sha1),
    Psha2(Psha2),
    Sha256(Sha256),
    Sha384(Sha384),
    Sha512(Sha512),
    Sha3_224(Sha3_224),
    Sha3_256(Sha3_256),
    Sha3_384(Sha3_384),
    Sha3_512(Sha3_512),
}

impl Digest {
    /// Creates a digest from a typed hash which is a string that looks like
    /// `sha2_256:e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7`.
    pub fn from_typed_hash(typed_hash: &str) -> Result<Self, DigestError> {
        let (alg, hash) = typed_hash.split_once(':').ok_or(DigestError::InvalidDigestSpec)?;
        let decoded_hash = hex::decode(hash).map_err(|error| DigestError::HexDecodingError {
            name: alg.to_string(),
            value: hash.to_string(),
            source: error,
        })?;
        match alg {
            "psha2" => Ok(Digest::Psha2(Psha2::from(decoded_hash))),
            "sha1" => {
                let array: [u8; 20] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha1(Sha1::from(array)))
            }
            "sha256" | "sha2_256" | "sha2-256" => {
                let array: [u8; 32] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha256(Sha256::from(array)))
            }
            "sha384" | "sha2_384" | "sha2-384" => {
                let array: [u8; 48] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha384(Sha384::from(array)))
            }
            "sha512" | "sha2_512" | "sha2-512" => {
                let array: [u8; 64] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha512(Sha512::from(array)))
            }
            "sha3_224" | "sha3-224" => {
                let array: [u8; 28] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha3_224(Sha3_224::from(array)))
            }
            "sha3_256" | "sha3-256" => {
                let array: [u8; 32] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha3_256(Sha3_256::from(array)))
            }
            "sha3_384" | "sha3-384" => {
                let array: [u8; 48] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha3_384(Sha3_384::from(array)))
            }
            "sha3_512" | "sha3-512" => {
                let array: [u8; 64] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        source: hex::FromHexError::InvalidStringLength,
                    })?;
                Ok(Digest::Sha3_512(Sha3_512::from(array)))
            }
            _ => Err(DigestError::UnknownKey(alg.to_string())),
        }
    }

    pub fn to_typed_hash(&self) -> String {
        match self {
            Digest::Sha1(h) => h.to_typed_hash(),
            Digest::Psha2(h) => h.to_typed_hash(),
            Digest::Sha256(h) => h.to_typed_hash(),
            Digest::Sha384(h) => h.to_typed_hash(),
            Digest::Sha512(h) => h.to_typed_hash(),
            Digest::Sha3_224(h) => h.to_typed_hash(),
            Digest::Sha3_256(h) => h.to_typed_hash(),
            Digest::Sha3_384(h) => h.to_typed_hash(),
            Digest::Sha3_512(h) => h.to_typed_hash(),
        }
    }
}

impl From<Sha1> for Digest {
    fn from(h: Sha1) -> Self {
        Digest::Sha1(h)
    }
}
impl From<Psha2> for Digest {
    fn from(h: Psha2) -> Self {
        Digest::Psha2(h)
    }
}
impl From<Sha256> for Digest {
    fn from(h: Sha256) -> Self {
        Digest::Sha256(h)
    }
}
impl From<Sha384> for Digest {
    fn from(h: Sha384) -> Self {
        Digest::Sha384(h)
    }
}
impl From<Sha512> for Digest {
    fn from(h: Sha512) -> Self {
        Digest::Sha512(h)
    }
}
impl From<Sha3_224> for Digest {
    fn from(h: Sha3_224) -> Self {
        Digest::Sha3_224(h)
    }
}
impl From<Sha3_256> for Digest {
    fn from(h: Sha3_256) -> Self {
        Digest::Sha3_256(h)
    }
}
impl From<Sha3_384> for Digest {
    fn from(h: Sha3_384) -> Self {
        Digest::Sha3_384(h)
    }
}
impl From<Sha3_512> for Digest {
    fn from(h: Sha3_512) -> Self {
        Digest::Sha3_512(h)
    }
}

impl From<Digest> for RawDigest {
    fn from(digest: Digest) -> Self {
        match digest {
            Digest::Sha1(h) => RawDigest { sha1: h.as_ref().to_vec(), ..Default::default() },
            Digest::Psha2(h) => RawDigest { psha2: h.as_ref().to_vec(), ..Default::default() },
            Digest::Sha256(h) => RawDigest { sha2_256: h.as_ref().to_vec(), ..Default::default() },
            Digest::Sha384(h) => RawDigest { sha2_384: h.as_ref().to_vec(), ..Default::default() },
            Digest::Sha512(h) => RawDigest { sha2_512: h.as_ref().to_vec(), ..Default::default() },
            Digest::Sha3_224(h) => {
                RawDigest { sha3_224: h.as_ref().to_vec(), ..Default::default() }
            }
            Digest::Sha3_256(h) => {
                RawDigest { sha3_256: h.as_ref().to_vec(), ..Default::default() }
            }
            Digest::Sha3_384(h) => {
                RawDigest { sha3_384: h.as_ref().to_vec(), ..Default::default() }
            }
            Digest::Sha3_512(h) => {
                RawDigest { sha3_512: h.as_ref().to_vec(), ..Default::default() }
            }
        }
    }
}

impl From<Digest> for HexDigest {
    fn from(digest: Digest) -> Self {
        match digest {
            Digest::Sha1(h) => HexDigest { sha1: hex::encode(h), ..Default::default() },
            Digest::Psha2(h) => HexDigest { psha2: hex::encode(h), ..Default::default() },
            Digest::Sha256(h) => HexDigest { sha2_256: hex::encode(h), ..Default::default() },
            Digest::Sha384(h) => HexDigest { sha2_384: hex::encode(h), ..Default::default() },
            Digest::Sha512(h) => HexDigest { sha2_512: hex::encode(h), ..Default::default() },
            Digest::Sha3_224(h) => HexDigest { sha3_224: hex::encode(h), ..Default::default() },
            Digest::Sha3_256(h) => HexDigest { sha3_256: hex::encode(h), ..Default::default() },
            Digest::Sha3_384(h) => HexDigest { sha3_384: hex::encode(h), ..Default::default() },
            Digest::Sha3_512(h) => HexDigest { sha3_512: hex::encode(h), ..Default::default() },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const HASH1: Sha256 = Sha256([
        0xe2, 0x7c, 0x68, 0x23, 0x57, 0x58, 0x9a, 0xc6, 0x6b, 0xf0, 0x65, 0x73, 0xda, 0x90, 0x84,
        0x69, 0xae, 0xae, 0xae, 0x5e, 0x73, 0xe4, 0xec, 0xc5, 0x25, 0xac, 0x5d, 0x4b, 0x88, 0x88,
        0x22, 0xe7,
    ]);
    const HASH2: Sha256 = Sha256([
        0x56, 0x49, 0xa7, 0x88, 0x2a, 0x83, 0xa8, 0xc1, 0xc3, 0x33, 0xdb, 0x04, 0x6f, 0xd0, 0xa6,
        0x0e, 0x9b, 0xac, 0xed, 0xb3, 0xca, 0xab, 0x3c, 0x91, 0x57, 0x8a, 0x7e, 0x21, 0xb1, 0xda,
        0x89, 0xe3,
    ]);

    #[test]
    fn test_digest_to_raw_digest_conversion() {
        let digest = Digest::Sha256(HASH2);
        let raw_digest: RawDigest = digest.into();
        assert_eq!(raw_digest.sha2_256, HASH2.as_ref());
    }

    #[test]
    fn test_digest_to_hex_digest_conversion() {
        let digest = Digest::Sha256(HASH1);
        let hex_digest: HexDigest = digest.into();
        assert_eq!(
            hex_digest.sha2_256,
            "e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7"
        );
    }

    #[test]
    fn test_digest_to_typed_hash_conversion() {
        let digest = Digest::Sha256(HASH1);
        let typed_hash = digest.to_typed_hash();
        assert_eq!(
            typed_hash,
            "sha256:e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7"
        );
        let back_again = Digest::from_typed_hash(&typed_hash).expect("conversion failed");
        assert_eq!(digest, back_again);
    }
}
