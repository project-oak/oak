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

use oak_proto_rust::oak::HexDigest;
use serde::Deserialize;
#[cfg(feature = "std")]
use serde::Serialize;
use time::OffsetDateTime;

/// Admissible predicate type of in-toto endorsement statements.
const PREDICATE_V1: &str = "https://github.com/project-oak/transparent-release/claim/v1";
pub const PREDICATE_V2: &str = "https://github.com/project-oak/transparent-release/claim/v2";

/// ClaimType for endorsements. Expected to be used together with `ClaimV1` as
/// the predicate type in an in-toto statement.
const ENDORSEMENT_V2: &str = "https://github.com/project-oak/transparent-release/endorsement/v2";

/// URI representing in-toto statements. We only use V1.
pub const STATEMENT_V1: &str = "https://in-toto.io/Statement/v1";

// A map from algorithm name to lowercase hex-encoded value.
pub type DigestSet = BTreeMap<String, String>;

/// A software artifact identified by its name and a set of artifacts.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct Subject {
    pub name: String,
    pub digest: DigestSet,
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

#[derive(Debug)]
pub enum InvalidClaimData {
    StatementType,
    PredicateType,
    ClaimType,
    Validity(String),
}

/// Detailed content of a claim.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct ClaimPredicate<S> {
    /// URI indicating the type of the claim. It determines the meaning of
    /// `claimSpec` and `evidence`.
    #[serde(rename = "claimType")]
    pub claim_type: String,
    /// A detailed description of the claim, as an optional arbitrary object.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "claimSpec")]
    pub claim_spec: Option<S>,
    // Specifies which evidence field the endorsement targets.
    // The `default` option should be removed once this is in operation.
    #[serde(default, rename = "usage")]
    pub usage: String,
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
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
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

/// Metadata about an artifact that serves as the evidence for the truth of a
/// claim.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct ClaimEvidence {
    /// Optional field specifying the role of this evidence within the claim.
    pub role: Option<String>,
    /// URI uniquely identifies this evidence.
    pub uri: String,
    /// Collection of cryptographic digests for the contents of this artifact.
    pub digest: DigestSet,
}

/// Inner type for a simple claim with no further fields.
#[derive(Debug, Deserialize, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct Claimless {}

pub type EndorsementStatement = Statement<ClaimPredicate<Claimless>>;

/// Converts the given byte array into an endorsement statement.
pub fn parse_endorsement_statement(bytes: &[u8]) -> anyhow::Result<EndorsementStatement> {
    serde_json::from_slice(bytes)
        .map_err(|error| anyhow::anyhow!("parsing endorsement bytes: {}", error))
}

/// Checks that the given statement is a valid claim:
/// - has valid Statement and Predicate types, and
/// - has a valid validity duration.
pub fn validate_claim<T>(claim: &Statement<ClaimPredicate<T>>) -> Result<(), InvalidClaimData> {
    if claim._type != STATEMENT_V1 {
        return Err(InvalidClaimData::StatementType);
    }
    if claim.predicate_type != PREDICATE_V1 && claim.predicate_type != PREDICATE_V2 {
        return Err(InvalidClaimData::PredicateType);
    }
    if let Some(validity) = &claim.predicate.validity {
        if validity.not_before < claim.predicate.issued_on {
            return Err(InvalidClaimData::Validity(String::from("notBefore before issuedOn")));
        }
        if validity.not_before > validity.not_after {
            return Err(InvalidClaimData::Validity(String::from("notBefore after notAfter")));
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
pub fn validate_endorsement(claim: &EndorsementStatement) -> Result<(), InvalidClaimData> {
    validate_claim(claim)?;
    if claim.predicate.claim_type != ENDORSEMENT_V2 {
        return Err(InvalidClaimData::ClaimType);
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
        _ => anyhow::bail!("unknown digest key in endorsement statement"),
    }

    Ok(())
}

/// Returns the digest found in the endorsement statement. This digest can
/// be from the binary or from the attachment.
pub fn get_digest(claim: &EndorsementStatement) -> anyhow::Result<HexDigest> {
    if claim.subject.len() != 1 {
        anyhow::bail!("expected a single endorsement subject, found {}", claim.subject.len());
    }

    let mut digest = HexDigest::default();
    claim.subject[0].digest.iter().try_fold(&mut digest, |acc, (key, value)| {
        set_digest_field_from_map_entry(acc, key.as_str(), value.as_str())?;
        Ok::<&mut HexDigest, anyhow::Error>(acc)
    })?;

    Ok(digest)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::get_digest;
    use crate::claims::{parse_endorsement_statement, validate_endorsement};

    const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";

    #[test]
    fn test_parse_endorsement_statement() {
        let endorsement_bytes = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement file");
        let claim = parse_endorsement_statement(&endorsement_bytes)
            .expect("couldn't parse bytes into a claim");

        assert!(validate_endorsement(&claim).is_ok())
    }

    #[test]
    fn test_get_claims() {
        let endorsement_bytes = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement file");
        let claim = parse_endorsement_statement(&endorsement_bytes)
            .expect("couldn't parse bytes into a claim");
        let digest = get_digest(&claim).expect("failed to get digest from claim");

        assert_eq!(
            digest.sha2_256,
            "18c34d8cc737fb5709a99acb073cdc5ed8a404503f626cea6e0bad0a406002fc"
        );
    }
}
