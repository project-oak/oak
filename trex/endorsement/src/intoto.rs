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
use core::str::FromStr;

use anyhow::{ensure, Context};
use chrono::{DateTime, FixedOffset};
use serde::{Deserialize, Serialize};

/// URI representing in-toto statements. We only use V1, earlier and later
/// versions will be rejected.
const STATEMENT_TYPE: &str = "https://in-toto.io/Statement/v1";

/// Current predicate type of in-toto endorsement statements, which loses
/// the `usage` field and adds claim types.
const PREDICATE_TYPE_V3: &str = "https://project-oak.github.io/oak/tr/endorsement/v1";

/// A map from algorithm name to lowercase hex-encoded value.
pub type DigestSet = BTreeMap<String, String>;

/// An artifact identified by its name and digest.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Subject {
    /// The name of the artifact.
    pub name: String,
    /// A map from algorithm name to lowercase hex-encoded value of the digest.
    pub digest: DigestSet,
}

/// Validity time range of an endorsement statement.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Validity {
    /// The timestamp from which the claim is
    /// effective.
    #[serde(rename = "notBefore")]
    pub not_before: DateTime<FixedOffset>,

    /// The timestamp from which the claim no longer
    /// applies to the artifact.
    #[serde(rename = "notAfter")]
    pub not_after: DateTime<FixedOffset>,
}

/// A single claim about the endorsement subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Claim {
    /// The type of the claim, as a URI.
    pub r#type: String,
}

/// The predicate part of an endorsement subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct EndorsementPredicate {
    /// The timestamp when the statement was created.
    #[serde(rename = "issuedOn")]
    pub issued_on: DateTime<FixedOffset>,

    /// Validity duration of this statement.
    #[serde(rename = "validity")]
    pub validity: Validity,

    /// A list of claims about the subject.
    #[serde(default)]
    pub claims: Vec<Claim>,
}

/// Represents a generic statement that binds a predicate to a subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Statement<P> {
    /// The type of the statement, as a URI.
    _type: String,
    /// The type of the predicate, as a URI.
    #[serde(rename = "predicateType")]
    predicate_type: String,
    /// The subject of the statement.
    pub subject: Vec<Subject>,
    /// The predicate of the statement.
    pub predicate: P,
}

/// An endorsement statement, which is a [`Statement`] with an
/// [`EndorsementPredicate`].
pub type EndorsementStatement = Statement<EndorsementPredicate>;

/// Options for creating a new [`EndorsementStatement`]. This acts as a
/// view on the user-settable fields in an EndorsementStatement.
pub struct EndorsementOptions {
    /// The timestamp when the statement was created.
    pub issued_on: DateTime<FixedOffset>,
    /// The validity duration of this statement.
    pub validity: Validity,
    /// A list of claims to be included in the statement.
    pub claims: Vec<String>,
}

impl EndorsementStatement {
    /// Creates a new endorsement statement.
    pub fn new(subject: Subject, options: EndorsementOptions) -> Self {
        EndorsementStatement {
            _type: STATEMENT_TYPE.to_string(),
            predicate_type: PREDICATE_TYPE_V3.to_string(),
            subject: vec![subject],
            predicate: EndorsementPredicate {
                issued_on: options.issued_on,
                validity: options.validity,
                claims: options.claims.into_iter().map(|claim| Claim { r#type: claim }).collect(),
            },
        }
    }

    /// Checks that the endorsement statement is valid, based on timestamp
    /// and required claims.
    pub fn validate(
        &self,
        validation_time: oak_time::Instant,
        claims: &[&str],
    ) -> anyhow::Result<()> {
        // Convert to DateTime<Utc> since that's what the Statement representation uses.
        let validation_time: DateTime<chrono::Utc> = validation_time.into();

        ensure!(self._type == STATEMENT_TYPE, "unsupported statement type");
        ensure!(self.predicate_type == PREDICATE_TYPE_V3, "unsupported predicate type");

        let validity = &self.predicate.validity;
        ensure!(validation_time >= validity.not_before, "the claim is not yet applicable");
        ensure!(validation_time <= validity.not_after, "the claim is no longer applicable");

        for claim_type in claims {
            self.predicate
                .claims
                .iter()
                .find(|k| &k.r#type == claim_type)
                .context("required claim type not found")?;
        }

        Ok(())
    }
}

impl FromStr for EndorsementStatement {
    type Err = anyhow::Error;

    /// Parses an endorsement statement from a string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        serde_json::from_str(s).context("trying to parse endorsement")
    }
}

impl TryFrom<&[u8]> for EndorsementStatement {
    type Error = anyhow::Error;

    /// Parses an endorsement statement from a byte slice.
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        serde_json::from_slice(value).context("trying to parse endorsement")
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use chrono::Duration;
    use oak_file_utils::data_path;

    use super::*;

    const ENDORSEMENT_PATH: &str = "trex/endorsement/testdata/endorsement.json";

    #[test]
    fn parse_string() -> anyhow::Result<()> {
        let raw = fs::read_to_string(data_path(ENDORSEMENT_PATH))?;
        let parsed: EndorsementStatement = raw.parse()?;

        assert_eq!(
            parsed,
            EndorsementStatement::new(
                Subject {
                    name: "oak_orchestrator".to_string(),
                    digest: BTreeMap::from([(
                        "sha256".to_string(),
                        "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc"
                            .to_string()
                    )])
                },
                EndorsementOptions {
                    issued_on: "2024-02-28T09:47:12.067000Z".parse()?,
                    validity: Validity {
                        not_before: "2024-02-28T09:47:12.067000Z".parse()?,
                        not_after: "2025-02-27T09:47:12.067000Z".parse()?,
                    },
                    claims: vec![
                        "https://project-oak.github.io/oak/test_claim_1".to_string(),
                        "https://project-oak.github.io/oak/test_claim_2".to_string(),
                    ]
                }
            )
        );

        Ok(())
    }

    #[test]
    fn parse_bytes() -> anyhow::Result<()> {
        let raw = fs::read(data_path(ENDORSEMENT_PATH))?;
        let parsed = EndorsementStatement::try_from(raw.as_slice())?;

        assert_eq!(
            parsed,
            EndorsementStatement::new(
                Subject {
                    name: "oak_orchestrator".to_string(),
                    digest: BTreeMap::from([(
                        "sha256".to_string(),
                        "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc"
                            .to_string()
                    )])
                },
                EndorsementOptions {
                    issued_on: "2024-02-28T09:47:12.067000Z".parse()?,
                    validity: Validity {
                        not_before: "2024-02-28T09:47:12.067000Z".parse()?,
                        not_after: "2025-02-27T09:47:12.067000Z".parse()?,
                    },
                    claims: vec![
                        "https://project-oak.github.io/oak/test_claim_1".to_string(),
                        "https://project-oak.github.io/oak/test_claim_2".to_string(),
                    ]
                }
            )
        );

        Ok(())
    }

    fn create_test_statement(
        issued_on: DateTime<FixedOffset>,
        valid_for: Duration,
        claims: Vec<String>,
    ) -> EndorsementStatement {
        let validity = Validity { not_before: issued_on, not_after: issued_on + valid_for };
        EndorsementStatement::new(
            Subject {
                name: "test_subject".to_string(),
                digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
            },
            EndorsementOptions { issued_on, validity, claims },
        )
    }

    #[test]
    fn validate_happy_path() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec!["claim1".to_string()]);

        let validation_time = now + Duration::hours(1);
        statement.validate(validation_time.to_utc().into(), &["claim1"])?;

        Ok(())
    }

    #[test]
    fn validate_unsupported_statement_type() {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z").unwrap();
        let mut statement = create_test_statement(now, Duration::days(1), vec![]);
        statement._type = "unsupported".to_string();

        let result = statement.validate(now.to_utc().into(), &[]);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "unsupported statement type");
    }

    #[test]
    fn validate_unsupported_predicate_type() {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z").unwrap();
        let mut statement = create_test_statement(now, Duration::days(1), vec![]);
        statement.predicate_type = "unsupported".to_string();

        let result = statement.validate(now.to_utc().into(), &[]);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "unsupported predicate type");
    }

    #[test]
    fn validate_before_not_before() {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z").unwrap();
        let statement = create_test_statement(now, Duration::days(1), vec![]);

        let validation_time = now - Duration::hours(1);
        let result = statement.validate(validation_time.to_utc().into(), &[]);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "the claim is not yet applicable");
    }

    #[test]
    fn validate_after_not_after() {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z").unwrap();
        let statement = create_test_statement(now, Duration::days(1), vec![]);

        let validation_time = now + Duration::days(2);
        let result = statement.validate(validation_time.to_utc().into(), &[]);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "the claim is no longer applicable");
    }

    #[test]
    fn validate_missing_claim() {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z").unwrap();
        let statement = create_test_statement(now, Duration::days(1), vec!["claim1".to_string()]);
        let expectations = &["claim2"];

        let result = statement.validate(now.to_utc().into(), expectations);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "required claim type not found");
    }
}
