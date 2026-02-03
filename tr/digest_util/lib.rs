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

//! Provides utilities related to digest protocol buffers.

#![no_std]

extern crate alloc;

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
};

use anyhow::Context;
use oak_proto_rust::oak::{HexDigest, RawDigest};
use sha2::{Digest, Sha256, Sha384, Sha512};

/// A map from algorithm name to lowercase hex-encoded value which represents
/// a `RawDigest` or `HexDigest` encoded as JSON.
pub type DigestSet = BTreeMap<String, String>;

pub fn hash_sha2_256(input: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hasher.finalize().into()
}

fn hash_sha2_512(input: &[u8]) -> [u8; 64] {
    let mut hasher = Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

fn hash_sha2_384(input: &[u8]) -> [u8; 48] {
    let mut hasher = Sha384::new();
    hasher.update(input);
    hasher.finalize().into()
}

/// Computes various digest formats of a binary array.
/// The empty arrays need to be filled, when we depend on SHA{1,3} hashers.
pub fn raw_digest_from_contents(contents: &[u8]) -> RawDigest {
    RawDigest {
        sha2_256: hash_sha2_256(contents).to_vec(),
        sha2_512: hash_sha2_512(contents).to_vec(),
        sha2_384: hash_sha2_384(contents).to_vec(),
        ..Default::default()
    }
}

/// Analogous to raw_digest_from_contents, but emits hex encoded digest.
pub fn hex_digest_from_contents(contents: &[u8]) -> HexDigest {
    raw_to_hex_digest(&raw_digest_from_contents(contents))
}

fn set_digest_field_from_map_entry(
    digest: &mut HexDigest,
    key: &str,
    value: &str,
) -> anyhow::Result<()> {
    match key {
        "psha2" => {
            if !digest.psha2.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.psha2.push_str(value);
        }
        "sha1" => {
            if !digest.sha1.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha1.push_str(value);
        }
        "sha256" | "sha2_256" => {
            if !digest.sha2_256.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha2_256.push_str(value);
        }
        "sha512" | "sha2_512" => {
            if !digest.sha2_512.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha2_512.push_str(value);
        }
        "sha3_512" => {
            if !digest.sha3_512.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha3_512.push_str(value);
        }
        "sha3_384" => {
            if !digest.sha3_384.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha3_384.push_str(value);
        }
        "sha3_256" => {
            if !digest.sha3_256.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha3_256.push_str(value);
        }
        "sha3_224" => {
            if !digest.sha3_224.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha3_224.push_str(value);
        }
        "sha384" | "sha2_384" => {
            if !digest.sha2_384.is_empty() {
                anyhow::bail!("duplicate key {}", key);
            }
            digest.sha2_384.push_str(value);
        }
        _ => anyhow::bail!("unknown digest key {key}"),
    }

    Ok(())
}

/// Converts a JSON digest set to an equivalent protocol buffer.
pub fn set_to_hex_digest(digest_set: &DigestSet) -> anyhow::Result<HexDigest> {
    let mut digest = HexDigest::default();
    digest_set.iter().try_fold(&mut digest, |acc, (key, value)| {
        set_digest_field_from_map_entry(acc, key.as_str(), value.as_str())?;
        Ok::<&mut HexDigest, anyhow::Error>(acc)
    })?;

    Ok(digest)
}

/// Converts a hex-encoded digest to an equivalent JSON digest set.
pub fn hex_to_set_digest(hex_digest: &HexDigest) -> DigestSet {
    let mut digest_set = DigestSet::new();

    macro_rules! insert_if_present {
        ($field:ident) => {
            if !hex_digest.$field.is_empty() {
                digest_set.insert(stringify!($field).into(), hex_digest.$field.clone());
            }
        };
    }

    macro_rules! insert_if_present_with_custom_key {
        ($field:ident, $key:literal) => {
            if !hex_digest.$field.is_empty() {
                digest_set.insert($key.into(), hex_digest.$field.clone());
            }
        };
    }

    insert_if_present!(psha2);
    insert_if_present!(sha1);
    insert_if_present_with_custom_key!(sha2_256, "sha256");
    insert_if_present_with_custom_key!(sha2_512, "sha512");
    insert_if_present!(sha3_512);
    insert_if_present!(sha3_384);
    insert_if_present!(sha3_256);
    insert_if_present!(sha3_224);
    insert_if_present_with_custom_key!(sha2_384, "sha384");

    digest_set
}

/// Creates a hex digest from a typed hash which is a string that looks like
/// `sha2_256:e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7`.
/// The resulting `HexDigest` has only a single populated field.
pub fn hex_digest_from_typed_hash(typed_hash: &str) -> anyhow::Result<HexDigest> {
    let (alg, hash) = typed_hash.split_once(':').context("invalid digest spec")?;
    let digest_set = DigestSet::from([(alg.to_string(), hash.to_string())]);
    set_to_hex_digest(&digest_set)
}

#[derive(PartialEq)]
pub enum MatchResult {
    Same = 0,
    Different = 1,
    Undecidable = 2,
    Contradictory = 3,
}

/// Compares two digests instances for equality.
///
/// All available fields in both inputs are taken into account for the decision.
/// If it is undesirable to include the weak sha1 hash in the decision simply
/// remove it from either input.
///
/// [`Same`] if underlying binaries are the same, [`Different`] if they differ.
/// [`Undecidable`] if the constellation in the protos doesn't provide enough
/// information, [`Contradictory`] if the constellation suggest same and
/// different at the same time. [`Undecidable`] and [`Contradictory`] usually
/// point to problems which are unlikely to be addressable at run time.
pub fn get_hex_digest_match(a: &HexDigest, b: &HexDigest) -> MatchResult {
    let mut same = 0;
    let mut different = 0;

    let mut compare = |a: &str, b: &str| {
        if !a.is_empty() && !b.is_empty() {
            if a == b {
                same += 1;
            } else {
                different += 1;
            }
        }
    };

    compare(&a.psha2, &b.psha2);
    compare(&a.sha1, &b.sha1);
    compare(&a.sha2_256, &b.sha2_256);
    compare(&a.sha2_512, &b.sha2_512);
    compare(&a.sha3_512, &b.sha3_512);
    compare(&a.sha3_384, &b.sha3_384);
    compare(&a.sha3_256, &b.sha3_256);
    compare(&a.sha3_224, &b.sha3_224);
    compare(&a.sha2_384, &b.sha2_384);

    #[allow(clippy::collapsible_else_if)]
    if same > 0 {
        if different > 0 { MatchResult::Contradictory } else { MatchResult::Same }
    } else {
        if different > 0 { MatchResult::Different } else { MatchResult::Undecidable }
    }
}

/// Compares two raw digests.
pub fn get_raw_digest_match(a: &RawDigest, b: &RawDigest) -> MatchResult {
    get_hex_digest_match(&raw_to_hex_digest(a), &raw_to_hex_digest(b))
}

/// Determines a match between two `HexDigest` instances.
pub fn is_hex_digest_match(actual: &HexDigest, expected: &HexDigest) -> anyhow::Result<()> {
    match get_hex_digest_match(actual, expected) {
        MatchResult::Same => Ok(()),
        MatchResult::Different => {
            Err(anyhow::anyhow!("mismatched digests: expected={expected:?} actual={actual:?}",))
        }
        MatchResult::Undecidable => Err(anyhow::anyhow!("invalid digests")),
        MatchResult::Contradictory => Err(anyhow::anyhow!("hash collision")),
    }
}

pub fn is_raw_digest_match(actual: &RawDigest, expected: &RawDigest) -> anyhow::Result<()> {
    match get_raw_digest_match(actual, expected) {
        MatchResult::Same => Ok(()),
        MatchResult::Different => {
            Err(anyhow::anyhow!("mismatched digests: expected={expected:?} actual={actual:?}",))
        }
        MatchResult::Undecidable => Err(anyhow::anyhow!("invalid digests")),
        MatchResult::Contradictory => Err(anyhow::anyhow!("hash collision")),
    }
}

/// Converts raw digest to hex digest.
pub fn raw_to_hex_digest(r: &RawDigest) -> HexDigest {
    HexDigest {
        psha2: hex::encode(&r.psha2),
        sha1: hex::encode(&r.sha1),
        sha2_256: hex::encode(&r.sha2_256),
        sha2_512: hex::encode(&r.sha2_512),
        sha3_512: hex::encode(&r.sha3_512),
        sha3_384: hex::encode(&r.sha3_384),
        sha3_256: hex::encode(&r.sha3_256),
        sha3_224: hex::encode(&r.sha3_224),
        sha2_384: hex::encode(&r.sha2_384),
    }
}

/// Converts hex digest to raw digest.
pub fn hex_to_raw_digest(h: &HexDigest) -> anyhow::Result<RawDigest> {
    let hex_decode = |field, name| {
        hex::decode(field).map_err(|error| {
            anyhow::anyhow!("could not decode field {name}: {error} (value {field})")
        })
    };

    let raw = RawDigest {
        psha2: hex_decode(&h.psha2, "psha2")?,
        sha1: hex_decode(&h.sha1, "sha1")?,
        sha2_256: hex_decode(&h.sha2_256, "sha2_256")?,
        sha2_512: hex_decode(&h.sha2_512, "sha2_512")?,
        sha3_512: hex_decode(&h.sha3_512, "sha3_512")?,
        sha3_384: hex_decode(&h.sha3_384, "sha3_384")?,
        sha3_256: hex_decode(&h.sha3_256, "sha3_256")?,
        sha3_224: hex_decode(&h.sha3_224, "sha3_224")?,
        sha2_384: hex_decode(&h.sha2_384, "sha2_384")?,
    };

    Ok(raw)
}

#[cfg(test)]
mod tests {
    use oak_proto_rust::oak::HexDigest;

    use super::*;
    use crate::alloc::borrow::ToOwned;

    const HASH1: &str = "e27c682357589ac66bf06573da908469aeaeae5e73e4ecc525ac5d4b888822e7";
    const HASH2: &str = "5649a7882a83a8c1c333db046fd0a60e9bacedb3caab3c91578a7e21b1da89e3";
    const HASH3: &str = "536c56245ccee62530dd5febd49821ba4a6161c0";
    const HASH4: &str = "fc5ed8a3ba1da6717da6031760a2deb45c52b836";

    #[test]
    fn test_convert() {
        let expected = raw_digest_from_contents(b"whatever");
        let hex_digest = raw_to_hex_digest(&expected);
        let actual = hex_to_raw_digest(&hex_digest).expect("conversion failed");
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_hex_digest_from_typed_hash() {
        let typed_hash = "sha2_256:".to_owned() + HASH1;
        let expected = HexDigest { sha2_256: HASH1.to_owned(), ..Default::default() };
        let actual = hex_digest_from_typed_hash(&typed_hash).expect("conversion failed");
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_both_empty_undecidable() {
        let empty = HexDigest { ..Default::default() };
        let result = get_hex_digest_match(&empty, &empty);
        assert!(result == MatchResult::Undecidable);
    }

    #[test]
    fn test_one_empty_undecidable() {
        let a =
            HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
        let empty = HexDigest { ..Default::default() };
        let result = get_hex_digest_match(&a, &empty);
        assert!(result == MatchResult::Undecidable);
    }

    #[test]
    fn test_same() {
        let a =
            HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
        let b =
            HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
        let result = get_hex_digest_match(&a, &b);
        assert!(result == MatchResult::Same);
    }

    #[test]
    fn test_different() {
        let a = HexDigest { sha2_256: HASH1.to_owned(), ..Default::default() };
        let b = HexDigest { sha2_256: HASH2.to_owned(), ..Default::default() };
        let result = get_hex_digest_match(&a, &b);
        assert!(result == MatchResult::Different);
    }

    #[test]
    fn test_contradictory() {
        let a =
            HexDigest { sha1: HASH3.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
        let b =
            HexDigest { sha1: HASH4.to_owned(), sha2_256: HASH1.to_owned(), ..Default::default() };
        let result = get_hex_digest_match(&a, &b);
        assert!(result == MatchResult::Contradictory);
    }
}
