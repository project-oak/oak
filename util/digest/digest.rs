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
    #[error("could not decode field {name}: {value}: {error_details}")]
    HexDecodingError { name: String, value: String, error_details: String },
    #[error("invalid digest length: expected {expected}, got {actual}")]
    InvalidDigestLength { expected: usize, actual: usize },
}

pub trait TypedDigest: AsRef<[u8]> {
    /// Returns the algorithm name of this digest.
    fn r#type(&self) -> &'static str;

    /// Returns the hex-encoded string representation of this digest.
    fn to_hex(&self) -> String {
        hex::encode(self.as_ref())
    }

    /// Returns a prefixed typed hash of this digest (e.g. `sha2-256:<hex>`).
    fn to_typed_hash(&self) -> String {
        format!("{}:{}", self.r#type(), self.to_hex())
    }
}

/// Derives inherent methods of `TypedDigest` as a workaround which allows
/// callers to invoke `.to_hex()` and `.to_typed_hash()` on the digest types
/// without needing to import the `TypedDigest` trait.
macro_rules! derive_inherent_named_digest {
    ($($t:ty),*) => {
        $(
            impl $t {
                pub fn to_hex(&self) -> String {
                    <Self as crate::TypedDigest>::to_hex(self)
                }

                pub fn to_typed_hash(&self) -> String {
                    <Self as crate::TypedDigest>::to_typed_hash(self)
                }
            }
        )*
    };
}

derive_inherent_named_digest!(
    Psha2, Sha1, Sha256, Sha384, Sha512, Sha3_224, Sha3_256, Sha3_384, Sha3_512, Digest
);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Psha2(Vec<u8>);

impl Psha2 {
    pub fn from_contents(_input: &[u8]) -> Self {
        todo!("unimplemented")
    }
}

impl TypedDigest for Psha2 {
    fn r#type(&self) -> &'static str {
        "psha2"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha1([u8; 20]);

impl TypedDigest for Sha1 {
    fn r#type(&self) -> &'static str {
        "sha1"
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
}

impl TypedDigest for Sha256 {
    fn r#type(&self) -> &'static str {
        "sha2-256"
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
}

impl TypedDigest for Sha384 {
    fn r#type(&self) -> &'static str {
        "sha2-384"
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
}

impl TypedDigest for Sha512 {
    fn r#type(&self) -> &'static str {
        "sha2-512"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_224([u8; 28]);

impl TypedDigest for Sha3_224 {
    fn r#type(&self) -> &'static str {
        "sha3-224"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_256([u8; 32]);

impl TypedDigest for Sha3_256 {
    fn r#type(&self) -> &'static str {
        "sha3-256"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_384([u8; 48]);

impl TypedDigest for Sha3_384 {
    fn r#type(&self) -> &'static str {
        "sha3-384"
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_512([u8; 64]);

impl TypedDigest for Sha3_512 {
    fn r#type(&self) -> &'static str {
        "sha3-512"
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
impl TryFrom<Vec<u8>> for Sha256 {
    type Error = DigestError;
    fn try_from(v: Vec<u8>) -> Result<Self, Self::Error> {
        let len = v.len();
        Ok(Self(
            v.try_into()
                .map_err(|_| DigestError::InvalidDigestLength { expected: 32, actual: len })?,
        ))
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

impl AsRef<[u8]> for Psha2 {
    fn as_ref(&self) -> &[u8] {
        &self.0
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

impl From<Psha2> for Vec<u8> {
    fn from(val: Psha2) -> Self {
        val.0
    }
}
impl From<Sha1> for Vec<u8> {
    fn from(val: Sha1) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha256> for Vec<u8> {
    fn from(val: Sha256) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha384> for Vec<u8> {
    fn from(val: Sha384) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha512> for Vec<u8> {
    fn from(val: Sha512) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha3_224> for Vec<u8> {
    fn from(val: Sha3_224) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha3_256> for Vec<u8> {
    fn from(val: Sha3_256) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha3_384> for Vec<u8> {
    fn from(val: Sha3_384) -> Self {
        val.0.to_vec()
    }
}
impl From<Sha3_512> for Vec<u8> {
    fn from(val: Sha3_512) -> Self {
        val.0.to_vec()
    }
}

impl From<Sha1> for [u8; 20] {
    fn from(val: Sha1) -> Self {
        val.0
    }
}
impl From<Sha256> for [u8; 32] {
    fn from(val: Sha256) -> Self {
        val.0
    }
}
impl From<Sha384> for [u8; 48] {
    fn from(val: Sha384) -> Self {
        val.0
    }
}
impl From<Sha512> for [u8; 64] {
    fn from(val: Sha512) -> Self {
        val.0
    }
}
impl From<Sha3_224> for [u8; 28] {
    fn from(val: Sha3_224) -> Self {
        val.0
    }
}
impl From<Sha3_256> for [u8; 32] {
    fn from(val: Sha3_256) -> Self {
        val.0
    }
}
impl From<Sha3_384> for [u8; 48] {
    fn from(val: Sha3_384) -> Self {
        val.0
    }
}
impl From<Sha3_512> for [u8; 64] {
    fn from(val: Sha3_512) -> Self {
        val.0
    }
}

/// Represents a specific digest type and its (mostly) fixed-size data.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Digest {
    Psha2(Psha2),
    Sha1(Sha1),
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
            error_details: error.to_string(),
        })?;
        match alg {
            "psha2" => Ok(Digest::Psha2(Psha2::from(decoded_hash))),
            "sha1" => {
                let array: [u8; 20] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha1(Sha1::from(array)))
            }
            "sha256" | "sha2_256" | "sha2-256" => {
                let array: [u8; 32] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha256(Sha256::from(array)))
            }
            "sha384" | "sha2_384" | "sha2-384" => {
                let array: [u8; 48] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha384(Sha384::from(array)))
            }
            "sha512" | "sha2_512" | "sha2-512" => {
                let array: [u8; 64] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha512(Sha512::from(array)))
            }
            "sha3_224" | "sha3-224" => {
                let array: [u8; 28] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha3_224(Sha3_224::from(array)))
            }
            "sha3_256" | "sha3-256" => {
                let array: [u8; 32] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha3_256(Sha3_256::from(array)))
            }
            "sha3_384" | "sha3-384" => {
                let array: [u8; 48] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha3_384(Sha3_384::from(array)))
            }
            "sha3_512" | "sha3-512" => {
                let array: [u8; 64] =
                    decoded_hash.try_into().map_err(|_| DigestError::HexDecodingError {
                        name: alg.to_string(),
                        value: hash.to_string(),
                        error_details: hex::FromHexError::InvalidStringLength.to_string(),
                    })?;
                Ok(Digest::Sha3_512(Sha3_512::from(array)))
            }
            _ => Err(DigestError::UnknownKey(alg.to_string())),
        }
    }
}

impl AsRef<[u8]> for Digest {
    fn as_ref(&self) -> &[u8] {
        match self {
            Digest::Psha2(h) => h.as_ref(),
            Digest::Sha1(h) => h.as_ref(),
            Digest::Sha256(h) => h.as_ref(),
            Digest::Sha384(h) => h.as_ref(),
            Digest::Sha512(h) => h.as_ref(),
            Digest::Sha3_224(h) => h.as_ref(),
            Digest::Sha3_256(h) => h.as_ref(),
            Digest::Sha3_384(h) => h.as_ref(),
            Digest::Sha3_512(h) => h.as_ref(),
        }
    }
}

impl TypedDigest for Digest {
    fn r#type(&self) -> &'static str {
        match self {
            Digest::Psha2(h) => h.r#type(),
            Digest::Sha1(h) => h.r#type(),
            Digest::Sha256(h) => h.r#type(),
            Digest::Sha384(h) => h.r#type(),
            Digest::Sha512(h) => h.r#type(),
            Digest::Sha3_224(h) => h.r#type(),
            Digest::Sha3_256(h) => h.r#type(),
            Digest::Sha3_384(h) => h.r#type(),
            Digest::Sha3_512(h) => h.r#type(),
        }
    }
}

impl From<Psha2> for Digest {
    fn from(h: Psha2) -> Self {
        Digest::Psha2(h)
    }
}
impl From<Sha1> for Digest {
    fn from(h: Sha1) -> Self {
        Digest::Sha1(h)
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
            Digest::Psha2(h) => RawDigest { psha2: h.as_ref().to_vec(), ..Default::default() },
            Digest::Sha1(h) => RawDigest { sha1: h.as_ref().to_vec(), ..Default::default() },
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
            Digest::Psha2(h) => HexDigest { psha2: hex::encode(h), ..Default::default() },
            Digest::Sha1(h) => HexDigest { sha1: hex::encode(h), ..Default::default() },
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

    const EXAMPLE_SHA256_HEX: &str =
        "e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7";

    fn example_sha256() -> Sha256 {
        Sha256(hex::decode(EXAMPLE_SHA256_HEX).unwrap().try_into().unwrap())
    }

    #[test]
    fn test_digest_to_raw_digest_conversion() {
        let digest = Digest::Sha256(example_sha256());
        let raw_digest: RawDigest = digest.into();
        assert_eq!(raw_digest.sha2_256, example_sha256().as_ref());
    }

    #[test]
    fn test_digest_to_hex_digest_conversion() {
        let digest = Digest::Sha256(example_sha256());
        let hex_digest: HexDigest = digest.into();
        assert_eq!(hex_digest.sha2_256, EXAMPLE_SHA256_HEX);
    }

    #[test]
    fn test_digest_to_typed_hash_conversion() {
        let digest = Digest::Sha256(example_sha256());
        let typed_hash = digest.to_typed_hash();
        assert_eq!(typed_hash, format!("sha2-256:{}", EXAMPLE_SHA256_HEX));
        let back_again = Digest::from_typed_hash(&typed_hash).expect("conversion failed");
        assert_eq!(digest, back_again);
    }

    #[test]
    fn test_digest_to_hex_conversion() {
        let digest = Digest::Sha256(example_sha256());
        assert_eq!(digest.to_hex(), EXAMPLE_SHA256_HEX);
    }
}
