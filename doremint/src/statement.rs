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

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec,
    vec::Vec,
};

use anyhow::Context;
use chrono::{DateTime, Duration, FixedOffset};
use oak_proto_rust::oak::HexDigest;
use serde::{Deserialize, Serialize};

/// URI representing in-toto statements. We only use V1, earlier and later
/// versions will be rejected.
pub const STATEMENT_TYPE: &str = "https://in-toto.io/Statement/v1";

/// Oldest predicate type for in-toto endorsement statements. References still
/// exist, but fully removing it will be easy.
#[deprecated = "Use PREDICATE_TYPE_V3"]
pub const PREDICATE_TYPE_V1: &str = "https://github.com/project-oak/transparent-release/claim/v1";

/// Previous predicate type of in-toto endorsement statements. In operation.
#[deprecated = "Use PREDICATE_TYPE_V3"]
pub const PREDICATE_TYPE_V2: &str = "https://github.com/project-oak/transparent-release/claim/v2";

/// Current predicate type of in-toto endorsement statements, which loses
/// the `usage` field and adds claim types.
pub const PREDICATE_TYPE_V3: &str = "https://project-oak.github.io/oak/tr/endorsement/v1";

// A map from algorithm name to lowercase hex-encoded value.
pub type DigestSet = BTreeMap<String, String>;

/// An artifact identified by its name and digest.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Subject {
    pub name: String,
    pub digest: DigestSet,
}

/// Validity time range of an endorsement statement.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Validity {
    /// The timestamp (encoded as an Epoch time) from which the claim is
    /// effective.
    #[serde(rename = "notBefore")]
    pub not_before: DateTime<FixedOffset>,

    /// The timestamp (encoded as an Epoch time) from which the claim no longer
    /// applies to the artifact.
    #[serde(rename = "notAfter")]
    pub not_after: DateTime<FixedOffset>,
}

// From Rust struct to protocol buffer.
impl From<&Validity> for oak_proto_rust::oak::Validity {
    fn from(value: &Validity) -> oak_proto_rust::oak::Validity {
        oak_proto_rust::oak::Validity {
            not_before: Some(prost_types::Timestamp {
                seconds: value.not_before.timestamp(),
                // Safe since `timestamp_subsec_nanos` is in [0, 999_999_999].
                nanos: value.not_before.timestamp_subsec_nanos() as i32,
            }),
            not_after: Some(prost_types::Timestamp {
                seconds: value.not_after.timestamp(),
                // Safe since `timestamp_subsec_nanos` is in [0, 999_999_999].
                nanos: value.not_after.timestamp_subsec_nanos() as i32,
            }),
        }
    }
}

// A single claim about the endorsement subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Claim {
    pub r#type: String,
}

/// The predicate part of an endorsement subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct DefaultPredicate {
    // Specifies how to interpret the endorsement subject.
    // The `default` option is needed to support predicate V2.
    #[serde(default, rename = "usage")]
    pub usage: String,

    /// The timestamp (encoded as an Epoch time) when the statement was created.
    #[serde(rename = "issuedOn")]
    pub issued_on: DateTime<FixedOffset>,

    /// Validity duration of this statement.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "validity")]
    pub validity: Option<Validity>,

    #[serde(default)]
    pub claims: Vec<Claim>,
}

/// Represents a generic statement that binds a predicate to a subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Statement<P> {
    pub _type: String,
    #[serde(rename = "predicateType")]
    pub predicate_type: String,
    pub subject: Vec<Subject>,
    pub predicate: P,
}

pub type DefaultStatement = Statement<DefaultPredicate>;

pub struct DefaultStatementOptions {
    pub issued_on: DateTime<FixedOffset>,
    pub validity: Duration,
    pub claims: Vec<String>,
}

impl Statement<DefaultPredicate> {
    pub fn new(subject: Subject, options: DefaultStatementOptions) -> Self {
        let not_before = options.issued_on;
        let not_after = options.issued_on + options.validity;

        DefaultStatement {
            _type: STATEMENT_TYPE.to_string(),
            predicate_type: PREDICATE_TYPE_V3.to_string(),
            subject: vec![subject],
            predicate: DefaultPredicate {
                usage: "".to_string(),
                issued_on: options.issued_on,
                validity: Some(Validity { not_before, not_after }),
                claims: options.claims.into_iter().map(|claim| Claim { r#type: claim }).collect(),
            },
        }
    }
}

/// Converts the given byte array into an endorsement statement.
pub fn parse_statement(bytes: &[u8]) -> anyhow::Result<DefaultStatement> {
    serde_json::from_slice(bytes).map_err(|error| anyhow::anyhow!("failed to parse: {}", error))
}

/// Checks that the given endorsement statement is valid, based on timestamp
/// and required claims.
pub fn validate_statement(
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
            let now = DateTime::from_timestamp_millis(now_utc_millis)
                .context("invalid `now_utc_millis`")?;
            if now < validity.not_before {
                anyhow::bail!("the claim is not yet applicable")
            }
            if validity.not_after < now {
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

    use super::*;

    const ENDORSEMENT_PATH: &str = "doremint/testdata/endorsement.json";

    // Minimum supported value for Timestamp: 0001-01-01 00:00:00.0 +00:00:00.
    const MIN_VALUE_SECONDS: i64 = -62_135_596_800;

    // Maximum supported value for Timestamp: 9999-12-31 23:59:59.0 +00:00:00
    const MAX_VALUE_SECONDS: i64 = 253_402_300_799;

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

    #[test]
    fn test_convert_validity_min_values() {
        let validity = Validity {
            not_before: DateTime::from_timestamp(MIN_VALUE_SECONDS, 0)
                .expect("out of range seconds")
                .fixed_offset(),
            not_after: DateTime::UNIX_EPOCH.fixed_offset(),
        };
        let actual = oak_proto_rust::oak::Validity::from(&validity);

        let expected = oak_proto_rust::oak::Validity {
            not_before: Some(prost_types::Timestamp { seconds: MIN_VALUE_SECONDS, nanos: 0 }),
            not_after: Some(prost_types::Timestamp { seconds: 0, nanos: 0 }),
        };
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_convert_validity_max_values() {
        let validity = Validity {
            not_before: DateTime::UNIX_EPOCH.fixed_offset(),
            not_after: DateTime::from_timestamp(MAX_VALUE_SECONDS, 0)
                .expect("out of range seconds")
                .fixed_offset(),
        };
        let actual = oak_proto_rust::oak::Validity::from(&validity);

        let expected = oak_proto_rust::oak::Validity {
            not_before: Some(prost_types::Timestamp { seconds: 0, nanos: 0 }),
            not_after: Some(prost_types::Timestamp { seconds: MAX_VALUE_SECONDS, nanos: 0 }),
        };
        assert_eq!(expected, actual);
    }
}
