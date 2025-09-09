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
    borrow::ToOwned,
    string::{String, ToString},
    vec,
    vec::Vec,
};

use anyhow::{ensure, Context};
use digest_util::{hex_to_set_digest, is_hex_digest_match, set_to_hex_digest, DigestSet};
use oak_proto_rust::oak::HexDigest;
use oak_time::Instant;
use serde::{Deserialize, Serialize};

/// URI representing in-toto statements. We only use V1, earlier and later
/// versions will be rejected.
const STATEMENT_TYPE: &str = "https://in-toto.io/Statement/v1";

/// Oldest predicate type for in-toto endorsement statements. References still
/// exist, but fully removing it will be easy.
#[deprecated = "Use PREDICATE_TYPE_V3"]
const PREDICATE_TYPE_V1: &str = "https://github.com/project-oak/transparent-release/claim/v1";

/// Previous predicate type of in-toto endorsement statements. In operation.
#[deprecated = "Use PREDICATE_TYPE_V3"]
const PREDICATE_TYPE_V2: &str = "https://github.com/project-oak/transparent-release/claim/v2";

/// Current predicate type of in-toto endorsement statements, which loses
/// the `usage` field and adds claim types.
const PREDICATE_TYPE_V3: &str = "https://project-oak.github.io/oak/tr/endorsement/v1";

/// An artifact identified by its name and digest.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Subject {
    /// The name of the artifact. Defaults to empty and may be absent.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub name: String,

    /// A map from algorithm name to lowercase hex-encoded value of the digest.
    pub digest: DigestSet,
}

/// Validity time range of an endorsement statement.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Validity {
    /// The timestamp from which the claim is effective.
    #[serde(rename = "notBefore", with = "oak_time::instant::rfc3339")]
    pub not_before: Instant,

    /// The timestamp after which the claim no longer applies to the artifact.
    #[serde(rename = "notAfter", with = "oak_time::instant::rfc3339")]
    pub not_after: Instant,
}

// From Rust struct to protocol buffer.
impl From<&Validity> for oak_proto_rust::oak::Validity {
    fn from(value: &Validity) -> oak_proto_rust::oak::Validity {
        let not_before = Some(value.not_before.into_timestamp());
        let not_after = Some(value.not_after.into_timestamp());
        oak_proto_rust::oak::Validity { not_before, not_after }
    }
}

// From protocol buffer to Rust struct.
impl TryFrom<&oak_proto_rust::oak::Validity> for Validity {
    type Error = &'static str;

    fn try_from(value: &oak_proto_rust::oak::Validity) -> Result<Self, Self::Error> {
        let not_before = Instant::from(value.not_before.ok_or("not_before missing")?);
        let not_after = Instant::from(value.not_after.ok_or("not_after missing")?);
        Ok(Validity { not_before, not_after })
    }
}

// A single claim about the endorsement subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Claim {
    /// The type of the claim as URI.
    pub r#type: String,
}

/// The predicate part of an endorsement subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct DefaultPredicate {
    // Specifies how to interpret the endorsement subject.
    // The `default` option is needed to support predicate V2.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub usage: String,

    /// The timestamp (encoded as an Epoch time) when the statement was created.
    #[serde(rename = "issuedOn", with = "oak_time::instant::rfc3339")]
    pub issued_on: Instant,

    /// Validity duration of this statement.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub validity: Option<Validity>,

    #[serde(default)]
    pub claims: Vec<Claim>,
}

/// Represents a generic statement that binds a predicate to a subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Statement<P> {
    /// The type of the intoto statement, as a URI.
    pub _type: String,

    /// The type of the predicate, as a URI.
    #[serde(rename = "predicateType")]
    pub predicate_type: String,

    /// The subject of the statement. Even though never used, we allow
    /// intoto statements referring to more than one subject.
    pub subject: Vec<Subject>,

    /// The predicate of the statement.
    pub predicate: P,
}

pub type DefaultStatement = Statement<DefaultPredicate>;

/// Parses the given serialized JSON into an endorsement statement.
pub fn parse_statement(bytes: &[u8]) -> anyhow::Result<DefaultStatement> {
    Ok(serde_json::from_slice(bytes)?)
}

/// Serializes an endorsement statement as JSON.
pub fn serialize_statement(statement: &DefaultStatement) -> anyhow::Result<Vec<u8>> {
    Ok(serde_json::to_vec(statement)?)
}

/// Creates an endorsement statement from ingredients.
pub fn make_statement(
    subject_name: &str,
    digest: &HexDigest,
    issued_on: Instant,
    not_before: Instant,
    not_after: Instant,
    claim_types: Vec<&str>,
) -> DefaultStatement {
    let digest_set = hex_to_set_digest(digest);

    DefaultStatement {
        _type: STATEMENT_TYPE.to_owned(),
        predicate_type: PREDICATE_TYPE_V3.to_owned(),
        subject: vec![Subject { name: subject_name.to_string(), digest: digest_set }],
        predicate: DefaultPredicate {
            usage: "".to_owned(), // Ignored with predicate V3, do not use.
            issued_on,
            validity: Some(Validity { not_before, not_after }),
            claims: claim_types.iter().map(|x| Claim { r#type: x.to_string() }).collect(),
        },
    }
}

/// Checks that the given endorsement statement is valid, based on timestamp
impl DefaultStatement {
    fn validate_subject(&self, digest: &HexDigest) -> anyhow::Result<()> {
        let actual = get_hex_digest_from_statement(self)?;
        is_hex_digest_match(digest, &actual).context("comparing subject digests")
    }

    fn validate_header(&self) -> anyhow::Result<()> {
        ensure!(self._type == STATEMENT_TYPE, "unsupported statement type");

        #[allow(deprecated)] // We still need to validate the older types.
        if self.predicate_type != PREDICATE_TYPE_V1
            && self.predicate_type != PREDICATE_TYPE_V2
            && self.predicate_type != PREDICATE_TYPE_V3
        {
            anyhow::bail!("unsupported predicate type");
        }

        Ok(())
    }

    /// Validates the entire endorsement statement.
    ///
    /// Verification of the subject digest will be skipped if the `digest`
    /// parameter is empty.
    pub fn validate(
        &self,
        digest: Option<HexDigest>,
        verification_time: Instant,
        required_claims: &[&str],
    ) -> anyhow::Result<()> {
        self.validate_header()?;
        if let Some(d) = digest {
            self.validate_subject(&d)?;
        }
        self.predicate.validate(verification_time, required_claims)
    }
}

/// Checks that the endorsement predicate is valid, based on timestamp and
/// required claims.
impl DefaultPredicate {
    pub fn validate(&self, current_time: Instant, required_claims: &[&str]) -> anyhow::Result<()> {
        match &self.validity {
            Some(validity) => {
                if current_time < validity.not_before {
                    anyhow::bail!("the claim is not yet applicable")
                }
                if validity.not_after < current_time {
                    anyhow::bail!("the claim is no longer applicable")
                }
            }
            None => anyhow::bail!("the validity field is not set"),
        }

        for claim_type in required_claims {
            self.claims
                .iter()
                .find(|k| &k.r#type == claim_type)
                .context("required claim type not found")?;
        }

        Ok(())
    }
}

/// Returns the digest of the statement's subject.
pub fn get_hex_digest_from_statement<T>(statement: &Statement<T>) -> anyhow::Result<HexDigest> {
    if statement.subject.len() != 1 {
        anyhow::bail!("expected a single subject, found {}", statement.subject.len());
    }

    let digest = set_to_hex_digest(&statement.subject[0].digest)?;
    Ok(digest)
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::fs;

    use oak_file_utils::data_path;
    use oak_time::Instant;

    use super::{get_hex_digest_from_statement, parse_statement, Validity};

    const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";

    // Minimum supported value for Timestamp: 0001-01-01 00:00:00.0 +00:00:00.
    const MIN_VALUE_MILLIS: i64 = -62_135_596_800_000;
    const MIN_VALUE_NANOS: i128 = 1_000_000 * MIN_VALUE_MILLIS as i128;

    // Maximum supported value for Timestamp: 9999-12-31 23:59:59.0 +00:00:00
    const MAX_VALUE_MILLIS: i64 = 253_402_300_799_000;
    const MAX_VALUE_NANOS: i128 = 1_000_000 * MAX_VALUE_MILLIS as i128;

    #[test]
    fn test_get_hex_digest_from_statement() {
        let endorsement = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
        let statement = parse_statement(&endorsement).expect("couldn't parse statement");
        let digest =
            get_hex_digest_from_statement(&statement).expect("failed to get digest from claim");

        assert_eq!(
            digest.sha2_256,
            "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc"
        );
    }

    #[test]
    fn test_convert_validity_left_min() {
        let expected = Validity {
            not_before: Instant::from_unix_nanos(MIN_VALUE_NANOS),
            not_after: Instant::from_unix_nanos(0),
        };
        let proto = oak_proto_rust::oak::Validity::from(&expected);
        let actual = Validity::try_from(&proto).expect("failed to convert");
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_convert_validity_left_max() {
        let expected = Validity {
            not_before: Instant::from_unix_nanos(0),
            not_after: Instant::from_unix_nanos(MAX_VALUE_NANOS),
        };
        let proto = oak_proto_rust::oak::Validity::from(&expected);
        let actual = Validity::try_from(&proto).expect("failed to convert");
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_convert_validity_right_min() {
        let expected: oak_proto_rust::oak::Validity = oak_proto_rust::oak::Validity {
            not_before: Some(Instant::from_unix_millis(MIN_VALUE_MILLIS).into_timestamp()),
            not_after: Some(Instant::from_unix_millis(0).into_timestamp()),
        };
        let statement = Validity::try_from(&expected).expect("failed to convert");
        let actual = oak_proto_rust::oak::Validity::from(&statement);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_convert_validity_right_max() {
        let expected: oak_proto_rust::oak::Validity = oak_proto_rust::oak::Validity {
            not_before: Some(Instant::from_unix_millis(0).into_timestamp()),
            not_after: Some(Instant::from_unix_millis(MAX_VALUE_MILLIS).into_timestamp()),
        };
        let statement = Validity::try_from(&expected).expect("failed to convert");
        let actual = oak_proto_rust::oak::Validity::from(&statement);
        assert_eq!(expected, actual);
    }
}
