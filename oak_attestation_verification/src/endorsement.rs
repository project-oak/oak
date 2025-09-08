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

//! Contains endorsement verification. All public calls must happen through
//! verify_endorsement() in lib.rs.

extern crate alloc;

use alloc::vec::Vec;

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use intoto::statement::{parse_statement, validate_statement, DefaultStatement};
use oak_proto_rust::oak::attestation::v1::{
    verifying_key_reference_value, EndorsementReferenceValue, KeyType, SignedEndorsement,
    VerifyingKeySet,
};

use crate::{
    rekor::{
        parse_rekor_log_entry, parse_rekor_log_entry_body, verify_rekor_log_entry,
        verify_rekor_log_entry_ecdsa,
    },
    util::{convert_pem_to_raw, equal_keys, verify_signature, verify_signature_ecdsa},
};

/// No attempt will be made to decode the attachment of a firmware-type
/// binary unless this claim is present in the endorsement.
pub(crate) const FIRMWARE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/10271.md";

/// No attempt will be made to decode the attachment of a kernel-type
/// binary unless this claim is present in the endorsement.
pub(crate) const KERNEL_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/98982.md";

/// Verifies a signed endorsement against a reference value.
///
/// Returns the parsed statement whenever the verification succeeds, or an error
/// otherwise.
///
/// `now_utc_millis`: The current time in milliseconds UTC since Unix Epoch.
/// `signed_endorsement`: The endorsement along with signature and (optional)
///     Rekor log entry.
/// `ref_value`: A reference value containing e.g. the public keys needed
///     for the verification. The deprecated fields `endorser_public_key` and
///     `rekor_public_key` will be ignored.
pub(crate) fn verify_endorsement(
    now_utc_millis: i64,
    signed_endorsement: &SignedEndorsement,
    ref_value: &EndorsementReferenceValue,
) -> anyhow::Result<DefaultStatement> {
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
    verify_signature(signature, &endorsement.serialized, endorser_key_set)
        .context("verifying signature")?;

    let statement =
        parse_statement(&endorsement.serialized).context("parsing endorsement statement")?;
    let claims: Vec<&str> = required_claims.claim_types.iter().map(|x| &**x).collect();
    validate_statement(now_utc_millis, &claims, &statement)
        .context("validating endorsement statement")?;

    let rekor_ref_value =
        ref_value.rekor.as_ref().context("no rekor key set in signed endorsement")?;
    match rekor_ref_value.r#type.as_ref() {
        Some(verifying_key_reference_value::Type::Skip(_)) => Ok(statement),
        Some(verifying_key_reference_value::Type::Verify(key_set)) => {
            let log_entry = &signed_endorsement.rekor_log_entry;
            if log_entry.is_empty() {
                anyhow::bail!("log entry unavailable but verification was requested");
            }
            verify_rekor_log_entry(log_entry, key_set, &endorsement.serialized, now_utc_millis)
                .context("verifying rekor log entry")?;
            verify_endorser_public_key(log_entry, signature.key_id, endorser_key_set)?;
            Ok(statement)
        }
        None => Err(anyhow::anyhow!("empty Rekor verifying key set reference value")),
    }
}

/// Verifies the binary endorsement against log entry and public keys.
///
/// `endorser_public_key` and `signature` must be present.
///
/// If `rekor_public_key` is present, then presence of the log entry is
/// required and the log entry will be verified. If `rekor_public_key`
/// is empty (not set), then verification is skipped no matter if the log
/// entry is present or not.
pub(crate) fn verify_binary_endorsement(
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
    validate_statement(now_utc_millis, &[], &statement)
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

fn verify_endorser_public_key(
    log_entry: &[u8],
    signature_key_id: u32,
    endorser_key_set: &VerifyingKeySet,
) -> anyhow::Result<()> {
    let key = endorser_key_set
        .keys
        .iter()
        .find(|k| k.key_id == signature_key_id)
        .ok_or_else(|| anyhow::anyhow!("could not find key id in key set"))?;
    match key.r#type() {
        KeyType::Undefined => anyhow::bail!("Undefined key type"),
        KeyType::EcdsaP256Sha256 => verify_endorser_public_key_ecdsa(log_entry, &key.raw),
    }
}

/// Verifies that the endorser public key coincides with the one contained in
/// the attestation.
fn verify_endorser_public_key_ecdsa(
    serialized_log_entry: &[u8],
    endorser_public_key: &[u8],
) -> anyhow::Result<()> {
    // TODO(#4231): Currently, we only check that the public keys are the same.
    // Should be updated to support verifying rolling keys.
    let log_entry = parse_rekor_log_entry(serialized_log_entry)?;
    let body = parse_rekor_log_entry_body(&log_entry).context("getting rekor log entry body")?;

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

pub(crate) fn is_firmware_type(statement: &DefaultStatement) -> bool {
    // TODO: b/369602264 - remove usage field in struct, remove checking it.
    statement.predicate.usage == "firmware"
        || statement.predicate.claims.iter().any(|x| x.r#type == FIRMWARE_CLAIM_TYPE)
}

pub(crate) fn is_kernel_type(statement: &DefaultStatement) -> bool {
    // TODO: b/369602264 - remove usage field in struct, remove checking it.
    statement.predicate.usage == "kernel"
        || statement.predicate.claims.iter().any(|x| x.r#type == KERNEL_CLAIM_TYPE)
}

#[cfg(test)]
mod tests;
