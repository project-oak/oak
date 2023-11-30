//
// Copyright 2023 The Project Oak Authors
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

//! Contains structs for specifying in-toto statements and claims about
//! software artifacts. See also
//! <https://github.com/project-oak/transparent-release/blob/main/pkg/claims/claim.go>,
//! <https://github.com/project-oak/transparent-release/blob/main/pkg/intoto/intoto.go>.

extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use anyhow::Context;
use serde::{Deserialize, Serialize};
use time::OffsetDateTime;

/// PredicateType which identifies a V1 Claim, for in-toto statements.
pub const CLAIM_V1: &str = "https://github.com/project-oak/transparent-release/claim/v1";

/// ClaimType for endorsements. Expected to be used together with `ClaimV1` as
/// the predicate type in an in-toto statement.
pub const ENDORSEMENT_V2: &str =
    "https://github.com/project-oak/transparent-release/endorsement/v2";

/// URI representing in-toto v01 statements. This is constant for all predicate
/// types.
pub const STATEMENT_INTOTO_V01: &str = "https://in-toto.io/Statement/v0.1";

// A map from algorithm name to lowercase hex-encoded value.
pub type DigestSet = BTreeMap<String, String>;

/// A software artifact identified by its name and a set of artifacts.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Subject {
    pub name: String,
    pub digest: DigestSet,
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

#[derive(Debug)]
pub enum InvalidClaimData {
    StatementType,
    PredicateType,
    ClaimType,
    Validity(String),
}

/// Detailed content of a claim.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct ClaimPredicate<S> {
    /// URI indicating the type of the claim. It determines the meaning of
    /// `claimSpec` and `evidence`.
    #[serde(rename = "claimType")]
    pub claim_type: String,
    /// A detailed description of the claim, as an optional arbitrary object.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "claimSpec")]
    pub claim_spec: Option<S>,
    /// The timestamp (encoded as an Epoch time) when the claim was issued.
    #[serde(with = "time::serde::rfc3339")]
    #[serde(rename = "issuedOn")]
    pub issued_on: OffsetDateTime,
    /// Validity duration of this claim.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "validity")]
    pub validity: Option<ClaimValidity>,
    /// A collection of artifacts that support the truth of the claim.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    #[serde(rename = "evidence")]
    pub evidence: Vec<ClaimEvidence>,
}

/// Validity time range of an issued claim.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct ClaimValidity {
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

/// Metadata about an artifact that serves as the evidence for the truth of a claim.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct ClaimEvidence {
    /// Optional field specifying the role of this evidence within the claim.
    pub role: Option<String>,
    /// URI uniquely identifies this evidence.
    pub uri: String,
    /// Collection of cryptographic digests for the contents of this artifact.
    pub digest: DigestSet,
}

#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct EndorsementStatement {}

/// Converts the given byte array into an endorsement statement.
pub fn parse_endorsement_statement(
    bytes: &[u8],
) -> anyhow::Result<Statement<ClaimPredicate<EndorsementStatement>>> {
    serde_json::from_slice(bytes).context("parsing endorsement bytes")
}

/// Checks that the given statement is a valid claim:
/// - has valid Statement and Predicate types, and
/// - has a valid validity duration.
pub fn validate_claim<T>(claim: &Statement<ClaimPredicate<T>>) -> Result<(), InvalidClaimData> {
    if claim._type != STATEMENT_INTOTO_V01 {
        return Err(InvalidClaimData::StatementType);
    }
    if claim.predicate_type != CLAIM_V1 {
        return Err(InvalidClaimData::PredicateType);
    }
    if let Some(validity) = &claim.predicate.validity {
        if validity.not_before < claim.predicate.issued_on {
            return Err(InvalidClaimData::Validity(String::from(
                "notBefore before issuedOn",
            )));
        }
        if validity.not_before > validity.not_after {
            return Err(InvalidClaimData::Validity(String::from(
                "notBefore after notAfter",
            )));
        }
    }

    Ok(())
}

/// Checks that the input claim has a validity duration, and that the specified
/// time is inside the validity period.
pub fn verify_validity_duration<T>(
    now_utc_millis: i64,
    claim: &Statement<ClaimPredicate<T>>,
) -> anyhow::Result<()> {
    match &claim.predicate.validity {
        Some(validity) => {
            if validity.not_before.unix_timestamp_nanos() / 1000000 > now_utc_millis.into() {
                anyhow::bail!("the claim is not yet applicable")
            }
            if validity.not_after.unix_timestamp_nanos() / 1000000 < now_utc_millis.into() {
                anyhow::bail!("the claim is no longer applicable")
            }
            Ok(())
        }
        None => anyhow::bail!("the validity field is not set"),
    }
}

/// Checks that the given endorsement statement is a valid and has the correct
/// claim type.
pub fn validate_endorsement(
    claim: &Statement<ClaimPredicate<EndorsementStatement>>,
) -> Result<(), InvalidClaimData> {
    validate_claim(claim)?;
    if claim.predicate.claim_type != ENDORSEMENT_V2 {
        return Err(InvalidClaimData::ClaimType);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::claims::{parse_endorsement_statement, validate_endorsement};
    use std::fs;

    const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";

    #[test]
    fn test_parse_endorsement_statement() {
        let endorsement_bytes = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement file");
        let claim = parse_endorsement_statement(&endorsement_bytes)
            .expect("couldn't parse bytes into a claim");

        assert!(validate_endorsement(&claim).is_ok())
    }
}
