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

//! Contains support for parsing in-toto endorsement statements. The parsing
//! and the struct hierarchy are public for clients.

extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec::Vec};

use anyhow::Context;
use oak_proto_rust::oak::HexDigest;
use serde::Deserialize;
#[cfg(feature = "std")]
use serde::Serialize;
use time::OffsetDateTime;

use crate::util::UnixTimestampMillis;

/// URI representing in-toto statements. We only use V1, earlier and later
/// versions will be rejected.
pub(crate) const STATEMENT_TYPE: &str = "https://in-toto.io/Statement/v1";

/// Oldest predicate type for in-toto endorsement statements. References still
/// exist, but fully removing it will be easy.
#[deprecated = "Use PREDICATE_TYPE_V3"]
const PREDICATE_TYPE_V1: &str = "https://github.com/project-oak/transparent-release/claim/v1";

/// Previous predicate type of in-toto endorsement statements. In operation.
#[deprecated = "Use PREDICATE_TYPE_V3"]
const PREDICATE_TYPE_V2: &str = "https://github.com/project-oak/transparent-release/claim/v2";

/// Current predicate type of in-toto endorsement statements, which loses
/// the `usage` field and adds claim types.
pub(crate) const PREDICATE_TYPE_V3: &str = "https://project-oak.github.io/oak/tr/endorsement/v1";

// A map from algorithm name to lowercase hex-encoded value.
pub type DigestSet = BTreeMap<String, String>;

/// An artifact identified by its name and digest.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct Subject {
    pub name: String,
    pub digest: DigestSet,
}

/// Validity time range of an endorsement statement.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct Validity {
    /// The timestamp (encoded as an Epoch time) from which the claim is
    /// effective.
    #[serde(with = "time::serde::rfc3339")]
    #[serde(rename = "notBefore")]
    pub not_before: OffsetDateTime,

    /// The timestamp (encoded as an Epoch time) from which the claim no longer
    /// applies to the artifact.
    #[serde(with = "time::serde::rfc3339")]
    #[serde(rename = "notAfter")]
    pub not_after: OffsetDateTime,
}

// A single claim about the endorsement subject.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct Claim {
    pub r#type: String,
}

/// The predicate part of an endorsement subject.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct DefaultPredicate {
    // Specifies how to interpret the endorsement subject.
    // The `default` option is needed to support predicate V2.
    #[serde(default, rename = "usage")]
    pub usage: String,

    /// The timestamp (encoded as an Epoch time) when the statement was created.
    #[serde(with = "time::serde::rfc3339")]
    #[serde(rename = "issuedOn")]
    pub issued_on: OffsetDateTime,

    /// Validity duration of this statement.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "validity")]
    pub validity: Option<Validity>,

    #[serde(default)]
    pub claims: Vec<Claim>,
}

/// Represents a generic statement that binds a predicate to a subject.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct Statement<P> {
    pub _type: String,
    #[serde(rename = "predicateType")]
    pub predicate_type: String,
    pub subject: Vec<Subject>,
    pub predicate: P,
}

pub type DefaultStatement = Statement<DefaultPredicate>;

/// Converts the given byte array into an endorsement statement.
pub fn parse_statement(bytes: &[u8]) -> anyhow::Result<DefaultStatement> {
    serde_json::from_slice(bytes).map_err(|error| anyhow::anyhow!("failed to parse: {}", error))
}

/// Checks that the given endorsement statement is valid, based on timestamp
/// and required claims.
pub(crate) fn validate_statement(
    now_utc_millis: i64,
    required_claims: &[&str],
    statement: &DefaultStatement,
) -> anyhow::Result<()> {
    if statement._type != STATEMENT_TYPE {
        anyhow::bail!("unsupported statement type");
    }
    #[allow(deprecated)] // We still need to validate the older types.
    if statement.predicate_type != PREDICATE_TYPE_V1
        && statement.predicate_type != PREDICATE_TYPE_V2
        && statement.predicate_type != PREDICATE_TYPE_V3
    {
        anyhow::bail!("unsupported predicate type");
    }

    match &statement.predicate.validity {
        Some(validity) => {
            if validity.not_before.unix_timestamp_millis() > now_utc_millis {
                anyhow::bail!("the claim is not yet applicable")
            }
            if validity.not_after.unix_timestamp_millis() < now_utc_millis {
                anyhow::bail!("the claim is no longer applicable")
            }
        }
        None => anyhow::bail!("the validity field is not set"),
    }

    for claim_type in required_claims {
        statement
            .predicate
            .claims
            .iter()
            .find(|k| &k.r#type == claim_type)
            .context("required claim type not found")?;
    }

    Ok(())
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

/// Returns the digest of the statement's subject.
pub fn get_digest<T>(statement: &Statement<T>) -> anyhow::Result<HexDigest> {
    if statement.subject.len() != 1 {
        anyhow::bail!("expected a single subject, found {}", statement.subject.len());
    }

    let mut digest = HexDigest::default();
    statement.subject[0].digest.iter().try_fold(&mut digest, |acc, (key, value)| {
        set_digest_field_from_map_entry(acc, key.as_str(), value.as_str())?;
        Ok::<&mut HexDigest, anyhow::Error>(acc)
    })?;

    Ok(digest)
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::fs;

    use oak_file_utils::data_path;

    use super::{get_digest, parse_statement};

    const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";

    #[test]
    fn test_get_digest() {
        let endorsement = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
        let statement = parse_statement(&endorsement).expect("couldn't parse statement");
        let digest = get_digest(&statement).expect("failed to get digest from claim");

        assert_eq!(
            digest.sha2_256,
            "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc"
        );
    }
}
