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

//! Verifies endorsements as coming from Transparent Release.
//! Contains support for generating and parsing in-toto statements.

extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec, vec::Vec};

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_proto_rust::oak::{
    attestation::v1::{
        verifying_key_reference_value, EndorsementReferenceValue, KeyType, SignedEndorsement,
        VerifyingKeySet,
    },
    HexDigest,
};
use serde::Deserialize;
#[cfg(feature = "std")]
use serde::Serialize;
use time::OffsetDateTime;

use crate::{
    rekor::{get_rekor_log_entry_body, verify_rekor_log_entry, verify_rekor_log_entry_ecdsa},
    util::{
        convert_pem_to_raw, equal_keys, verify_signature, verify_signature_ecdsa,
        UnixTimestampMillis,
    },
};

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

/// No attempt will be made to decode the attachment of a firmware-type
/// binary unless this claim is present in the endorsement.
pub(crate) const FIRMWARE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/10271.md";

/// No attempt will be made to decode the attachment of a kernel-type
/// binary unless this claim is present in the endorsement.
pub(crate) const KERNEL_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/98982.md";

// A map from algorithm name to lowercase hex-encoded value.
type DigestSet = BTreeMap<String, String>;

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

pub fn is_firmware_type(statement: &DefaultStatement) -> bool {
    // TODO: b/369602264 - remove usage field in struct, remove checking it.
    return statement.predicate.usage == "firmware"
        || statement.predicate.claims.iter().any(|x| x.r#type == FIRMWARE_CLAIM_TYPE);
}

pub fn is_kernel_type(statement: &DefaultStatement) -> bool {
    // TODO: b/369602264 - remove usage field in struct, remove checking it.
    return statement.predicate.usage == "kernel"
        || statement.predicate.claims.iter().any(|x| x.r#type == KERNEL_CLAIM_TYPE);
}

/// Verifies a signed endorsement against a reference value.
///
/// Returns the parsed statement whenever the verification succeeds, or an error
/// otherwise.
///
/// `now_utc_millis`: The current time in milliseconds UTC since Unix Epoch.
/// `signed_endorsement`: The endorsement along with signature and (optional)
///     Rekor log entry.
/// `ref_value`: A reference value containing e.g. the public keys needed
///     for the verification.
pub fn verify_endorsement(
    now_utc_millis: i64,
    signed_endorsement: &SignedEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<DefaultStatement> {
    // Reject ref_value instances using the potentially deprecated fields.
    if !ref_value.endorser_public_key.is_empty() || !ref_value.rekor_public_key.is_empty() {
        anyhow::bail!("verify_endorsement does not support the deprecated fields");
    }

    let endorsement =
        signed_endorsement.endorsement.as_ref().context("no endorsement in signed endorsement")?;
    let signature =
        signed_endorsement.signature.as_ref().context("no signature in signed endorsement")?;
    let endorser_key_set =
        ref_value.endorser.as_ref().context("no endorser key set in signed endorsement")?;
    let required_claims = ref_value.required_claims.as_ref().context("required claims missing")?;

    // The signature verification is also part of log entry verification,
    // so in some cases this check will be dispensable. We verify the
    // signature nonetheless before parsing the endorsement.
    verify_signature(&signature, &endorsement.serialized, &endorser_key_set)
        .context("verifying signature")?;

    let statement =
        parse_statement(&endorsement.serialized).context("parsing endorsement statement")?;
    let claims: Vec<&str> = required_claims.claim_types.iter().map(|x| &**x).collect();
    validate_statement(now_utc_millis, &claims, &statement)
        .context("verifying endorsement statement")?;

    let rekor_ref_value =
        ref_value.rekor.as_ref().context("no rekor key set in signed endorsement")?;
    return match rekor_ref_value.r#type.as_ref() {
        Some(verifying_key_reference_value::Type::Skip(_)) => Ok(statement),
        Some(verifying_key_reference_value::Type::Verify(key_set)) => {
            let log_entry = &signed_endorsement.rekor_log_entry;
            if log_entry.is_empty() {
                anyhow::bail!("log entry unavailable but verification was requested");
            }
            verify_rekor_log_entry(log_entry, key_set, &endorsement.serialized)
                .context("verifying rekor log entry")?;
            verify_endorser_public_key(log_entry, signature.key_id, endorser_key_set)?;
            Ok(statement)
        }
        None => Err(anyhow::anyhow!("empty Rekor verifying key set reference value")),
    };
}

/// Verifies the binary endorsement against log entry and public keys.
///
/// `endorser_public_key` and `signature` must be present.
///
/// If `rekor_public_key` is present, then presence of the log entry is
/// required and the log entry will be verified. If `rekor_public_key`
/// is empty (not set), then verification is skipped no matter if the log
/// entry is present or not.
pub fn verify_binary_endorsement(
    now_utc_millis: i64,
    endorsement: &[u8],
    signature: &[u8],
    log_entry: &[u8],
    endorser_public_key: &[u8],
    rekor_public_key: &[u8],
) -> anyhow::Result<()> {
    if signature.is_empty() {
        anyhow::bail!("signature of endorsement is required");
    }
    if endorser_public_key.is_empty() {
        anyhow::bail!("endorser's public key is required");
    }

    // The signature verification is also part of log entry verification,
    // so in some cases this check will be dispensable. We verify the
    // signature nonetheless before parsing the endorsement.
    verify_signature_ecdsa(signature, endorsement, endorser_public_key)
        .context("verifying signature")?;

    let statement = parse_statement(endorsement).context("parsing endorsement statement")?;
    validate_statement(now_utc_millis, &vec![], &statement)
        .context("verifying endorsement statement")?;

    if !rekor_public_key.is_empty() {
        if log_entry.is_empty() {
            anyhow::bail!("log entry unavailable but verification was requested");
        }
        verify_rekor_log_entry_ecdsa(log_entry, rekor_public_key, endorsement)
            .context("verifying rekor log entry")?;
        verify_endorser_public_key_ecdsa(log_entry, endorser_public_key)
            .context("verifying endorser public key")?;
    }

    Ok(())
}

pub fn verify_endorser_public_key(
    log_entry: &[u8],
    signature_key_id: u32,
    endorser_key_set: &VerifyingKeySet,
) -> anyhow::Result<()> {
    let key = endorser_key_set
        .keys
        .iter()
        .find(|k| k.key_id == signature_key_id)
        .ok_or_else(|| anyhow::anyhow!("could not find key id in key set"))?;
    return match key.r#type() {
        KeyType::Undefined => anyhow::bail!("Undefined key type"),
        KeyType::EcdsaP256Sha256 => verify_endorser_public_key_ecdsa(log_entry, &key.raw),
    };
}

/// Verifies that the endorser public key coincides with the one contained in
/// the attestation.
pub fn verify_endorser_public_key_ecdsa(
    log_entry: &[u8],
    endorser_public_key: &[u8],
) -> anyhow::Result<()> {
    // TODO(#4231): Currently, we only check that the public keys are the same.
    // Should be updated to support verifying rolling keys.

    let body = get_rekor_log_entry_body(log_entry).context("getting rekor log entry body")?;

    let actual_pem_vec =
        BASE64_STANDARD.decode(body.spec.signature.public_key.content).map_err(|error| {
            anyhow::anyhow!("couldn't base64-decode public key bytes from server: {}", error)
        })?;
    let actual_pem =
        core::str::from_utf8(&actual_pem_vec).map_err(|error| anyhow::anyhow!(error))?;
    let actual = convert_pem_to_raw(actual_pem)
        .map_err(|e| anyhow::anyhow!(e))
        .context("converting public key from log entry body")?;

    if !equal_keys(endorser_public_key, &actual)? {
        anyhow::bail!(
            "endorser public key mismatch: expected {:?} found {:?}",
            endorser_public_key,
            actual,
        )
    }

    Ok(())
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
            if validity.not_before.unix_timestamp_millis() > now_utc_millis.into() {
                anyhow::bail!("the claim is not yet applicable")
            }
            if validity.not_after.unix_timestamp_millis() < now_utc_millis.into() {
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
mod tests;
