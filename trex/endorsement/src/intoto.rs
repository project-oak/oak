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
    vec::Vec,
};
use core::str::FromStr;

use anyhow::{anyhow, ensure, Context};
use chrono::{DateTime, FixedOffset};
use oci_spec::distribution::Reference as OciReference;
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
    /// The name of the artifact. Default to empty string.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub name: String,
    /// A map from algorithm name to lowercase hex-encoded value of the digest.
    pub digest: DigestSet,
}

/// Converts an OCI image reference to an endorsement Subject.
impl TryFrom<&OciReference> for Subject {
    type Error = anyhow::Error;

    fn try_from(image: &OciReference) -> Result<Self, Self::Error> {
        let name = image.repository().to_string();
        let digest = image.digest().ok_or_else(|| anyhow!("image reference must have a digest"))?;
        let (alg, digest) = digest.split_once(':').context("invalid image digest format")?;

        Ok(Subject { name, digest: DigestSet::from([(alg.to_string(), digest.to_string())]) })
    }
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
    /// In-ToTo statements allow more than one subject, but
    /// we don't want that and require exactly one.
    subject: [Subject; 1],
    /// The predicate of the statement.
    predicate: P,
}

impl<P> Statement<P> {
    /// The subject this statement applies to.
    pub fn subject(&self) -> &Subject {
        &self.subject[0]
    }

    /// The predicate this statement applies to.
    pub fn predicate(&self) -> &P {
        &self.predicate
    }
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
            subject: [subject],
            predicate: EndorsementPredicate {
                issued_on: options.issued_on,
                validity: options.validity,
                claims: options.claims.into_iter().map(|claim| Claim { r#type: claim }).collect(),
            },
        }
    }

    /// Creates a new endorsement statement for an OCI container image
    /// based on the image's reference.
    ///
    /// The image reference must use digests.
    pub fn from_container_image(
        image: &OciReference,
        options: EndorsementOptions,
    ) -> anyhow::Result<Self> {
        Ok(Self::new(image.try_into()?, options))
    }

    /// Checks that the endorsement statement is valid, based on timestamp
    /// and required claims.
    pub fn validate(
        &self,
        validation_time: oak_time::Instant,
        subject: &Subject,
        claims: &[&str],
    ) -> anyhow::Result<()> {
        // Convert to DateTime<Utc> since that's what the Statement representation uses.
        let validation_time: DateTime<chrono::Utc> = validation_time.into();

        let mut matching_digests = false;
        for (alg, digest) in &self.subject().digest {
            if let Some(self_digest) = subject.digest.get(alg) {
                ensure!(self_digest == digest, "subject digest mismatch for algorithm {}", alg);
                matching_digests = true;
            }
        }
        ensure!(matching_digests, "no matching digest algorithms in subject");

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
    use std::{boxed::Box, fs, vec};

    use chrono::Duration;
    use googletest::prelude::*;
    use oak_file_utils::data_path;

    use super::*;

    const ENDORSEMENT_PATH: &str = "trex/endorsement/testdata/endorsement.json";

    #[gtest]
    fn parse_string() -> anyhow::Result<()> {
        let raw = fs::read_to_string(data_path(ENDORSEMENT_PATH))?;
        let parsed: EndorsementStatement = raw.parse()?;

        assert_that!(
            parsed,
            eq(&EndorsementStatement::new(
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
            ))
        );

        Ok(())
    }

    #[gtest]
    fn parse_bytes() -> anyhow::Result<()> {
        let raw = fs::read(data_path(ENDORSEMENT_PATH))?;
        let parsed = EndorsementStatement::try_from(raw.as_slice())?;

        assert_that!(
            parsed,
            eq(&EndorsementStatement::new(
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
            ))
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

    #[gtest]
    fn from_container_image_happy_path() -> anyhow::Result<()> {
        let image_reference =
            "example.com/repository/image@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".parse()?;
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let options = EndorsementOptions {
            issued_on: now,
            validity: Validity { not_before: now, not_after: now + Duration::days(1) },
            claims: vec!["claim1".to_string()],
        };

        let statement = EndorsementStatement::from_container_image(&image_reference, options)?;

        assert_that!(
            statement,
            matches_pattern!(EndorsementStatement {
                subject: elements_are![eq(&Subject {
                    name: "repository/image".to_string(),
                    digest: BTreeMap::from([(
                        "sha256".to_string(),
                        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
                            .to_string()
                    )])
                })],
                ..
            })
        );

        Ok(())
    }

    #[gtest]
    fn from_container_image_no_digest() -> anyhow::Result<()> {
        let image_reference = "example.com/repository/image:latest".parse()?;
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let options = EndorsementOptions {
            issued_on: now,
            validity: Validity { not_before: now, not_after: now + Duration::days(1) },
            claims: vec![],
        };

        let result = EndorsementStatement::from_container_image(&image_reference, options);

        assert_that!(result, err(displays_as(eq("image reference must have a digest"))));

        Ok(())
    }

    #[gtest]
    fn validate_happy_path() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec!["claim1".to_string()]);

        let ref_claims = ["claim1"];
        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };

        let validation_time = now + Duration::hours(1);
        statement.validate(validation_time.to_utc().into(), &ref_subject, &ref_claims)?;

        Ok(())
    }

    #[gtest]
    fn validate_subject_name_mismatch_is_ok() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec!["claim1".to_string()]);

        let ref_claims = ["claim1"];
        let ref_subject = Subject {
            name: "other_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };

        let validation_time = now + Duration::hours(1);
        let result = statement.validate(validation_time.to_utc().into(), &ref_subject, &ref_claims);
        assert_that!(result, ok(()));

        Ok(())
    }

    #[gtest]
    fn validate_subject_digest_mismatch() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec!["claim1".to_string()]);

        let ref_claims = ["claim1"];
        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "01".to_string())]),
        };

        let validation_time = now + Duration::hours(1);
        let result = statement.validate(validation_time.to_utc().into(), &ref_subject, &ref_claims);
        assert_that!(result, err(displays_as(eq("subject digest mismatch for algorithm sha256"))));

        Ok(())
    }

    #[gtest]
    fn validate_no_matching_digest_algorithm() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec![]);

        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha512".to_string(), "00".to_string())]),
        };

        let validation_time = now + Duration::hours(1);
        let result = statement.validate(validation_time.to_utc().into(), &ref_subject, &[]);
        assert_that!(result, err(displays_as(eq("no matching digest algorithms in subject"))));

        Ok(())
    }

    #[gtest]
    fn validate_unsupported_statement_type() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let mut statement = create_test_statement(now, Duration::days(1), vec![]);
        statement._type = "unsupported".to_string();

        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };
        let result = statement.validate(now.to_utc().into(), &ref_subject, &[]);
        assert_that!(result, err(displays_as(eq("unsupported statement type"))));

        Ok(())
    }

    #[gtest]
    fn validate_unsupported_predicate_type() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let mut statement = create_test_statement(now, Duration::days(1), vec![]);
        statement.predicate_type = "unsupported".to_string();

        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };
        let result = statement.validate(now.to_utc().into(), &ref_subject, &[]);
        assert_that!(result, err(displays_as(eq("unsupported predicate type"))));

        Ok(())
    }

    #[gtest]
    fn validate_before_not_before() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec![]);

        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };
        let validation_time = now - Duration::hours(1);
        let result = statement.validate(validation_time.to_utc().into(), &ref_subject, &[]);
        assert_that!(result, err(displays_as(eq("the claim is not yet applicable"))));

        Ok(())
    }

    #[gtest]
    fn validate_after_not_after() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec![]);

        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };
        let validation_time = now + Duration::days(2);
        let result = statement.validate(validation_time.to_utc().into(), &ref_subject, &[]);
        assert_that!(result, err(displays_as(eq("the claim is no longer applicable"))));

        Ok(())
    }

    #[gtest]
    fn validate_missing_claim() -> anyhow::Result<()> {
        let now = DateTime::parse_from_rfc3339("2024-03-01T10:00:00.00Z")?;
        let statement = create_test_statement(now, Duration::days(1), vec!["claim1".to_string()]);
        let ref_claims = ["claim2"];
        let ref_subject = Subject {
            name: "test_subject".to_string(),
            digest: BTreeMap::from([("sha256".to_string(), "00".to_string())]),
        };

        let result = statement.validate(now.to_utc().into(), &ref_subject, &ref_claims);
        assert_that!(result, err(displays_as(eq("required claim type not found"))));

        Ok(())
    }
}
