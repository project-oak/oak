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

//! Provides JSON-related utilities for digests: Type `DigestSet` is intended
//! to be used as a JSON map as part of serde conversion.

use alloc::{collections::BTreeMap, string::String};

use oak_proto_rust::oak::HexDigest;

/// A map from algorithm name to lowercase hex-encoded value which represents
/// a `RawDigest` or `HexDigest` encoded as JSON.
pub type DigestSet = BTreeMap<String, String>;

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
