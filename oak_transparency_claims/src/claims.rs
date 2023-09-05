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

//! This module contains structs for specifying claims about software artifacts. The structs in
//! this module must be kept in sync with the structs defined in
//! <https://github.com/project-oak/transparent-release/blob/main/pkg/claims/claim.go>.

extern crate alloc;

use crate::intoto::{DigestSet, Statement, STATEMENT_INTOTO_V01};
use alloc::{string::String, vec::Vec};
use anyhow::Context;
use serde::{Deserialize, Serialize};
use time::OffsetDateTime;

/// URI representing the PredicateType of a V1 Claim. To be used in in-toto statements.
pub const CLAIM_V1: &str = "https://github.com/project-oak/transparent-release/claim/v1";

/// ClaimType for Endorsements. This is expected to be used together with `ClaimV1` as the predicate
/// type in an in-toto statement.
pub const ENDORSEMENT_V2: &str =
    "https://github.com/project-oak/transparent-release/endorsement/v2";

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

/// Convert the given byte array into an endorsement statement, or return an error.
pub fn parse_endorsement_statement(
    bytes: &[u8],
) -> anyhow::Result<Statement<ClaimPredicate<EndorsementStatement>>> {
    serde_json::from_slice(bytes).context("parsing endorsement bytes")
}

/// Check that the given statement is a valid claim:
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

/// Check that the input claim has a validity duration, and that the validity is not expired.
pub fn verify_validity_duration<T>(claim: &Statement<ClaimPredicate<T>>) -> anyhow::Result<()> {
    match &claim.predicate.validity {
        Some(validity) => {
            // We only compare the day, not the exact time.
            let today = OffsetDateTime::now_utc().to_julian_day();
            if validity.not_before.to_julian_day() > today {
                anyhow::bail!("the claim is not yet applicable")
            }
            if validity.not_after.to_julian_day() < today {
                anyhow::bail!("the claim is no longer applicable")
            }
            Ok(())
        }
        None => anyhow::bail!("the validity field is not set"),
    }
}

/// Check that the given endorsement statement, is a valid claim, and had the correct claim type.
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

    #[test]
    fn test_parse_endorsement_statement() {
        let endorsement_path = "testdata/endorsement.json";
        let endorsement_bytes = fs::read(endorsement_path).expect("couldn't read endorsement file");
        let claim = parse_endorsement_statement(&endorsement_bytes)
            .expect("couldn't parse bytes into a claim");

        assert!(validate_endorsement(&claim).is_ok())
    }
}
