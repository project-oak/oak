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

//! Contains endorsement verification. The actual exported function
//! is oak_attestation_verification::verify_endorsement() which differs
//! from the one here just in the return type.

#![no_std]

extern crate alloc;

use alloc::{vec, vec::Vec};

use anyhow::Context;
use intoto::statement::{parse_statement, DefaultStatement};
use key_util::{convert_pem_to_raw, verify_signature};
use oak_proto_rust::oak::attestation::v1::{
    endorsement::Format, verifying_key_reference_value, ClaimReferenceValue, Endorsement,
    EndorsementReferenceValue, KeyType, Signature, SignedEndorsement, SkipVerification,
    VerifyingKey, VerifyingKeyReferenceValue, VerifyingKeySet,
};
use oak_time::Instant;
use rekor::log_entry::{verify_rekor_log_entry, LogEntry};

/// No attempt will be made to decode the attachment of a firmware-type
/// binary unless this claim is present in the endorsement.
pub const FIRMWARE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/10271.md";

/// No attempt will be made to decode the attachment of a kernel-type
/// binary unless this claim is present in the endorsement.
pub const KERNEL_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/98982.md";

/// Creates a `SignedEndorsement` from ingredients.
pub fn create_signed_endorsement(
    serialized_endorsement: &[u8],
    serialized_signature: &[u8],
    key_id: u32,
) -> SignedEndorsement {
    let endorsement = Endorsement {
        format: Format::EndorsementFormatJsonIntoto.into(),
        serialized: serialized_endorsement.to_vec(),
        ..Default::default()
    };
    SignedEndorsement {
        endorsement: Some(endorsement),
        signature: Some(Signature { key_id, raw: serialized_signature.to_vec() }),
        ..Default::default()
    }
}

/// Creates an `EndorsementReferenceValue` from ingredients.
pub fn create_endorsement_reference_value(
    endorser_key: VerifyingKey,
    rekor_key: Option<VerifyingKey>,
) -> EndorsementReferenceValue {
    let rekor_key_set =
        rekor_key.map(|v| VerifyingKeySet { keys: [v].to_vec(), ..Default::default() });
    let rekor = create_verifying_key_reference_value(rekor_key_set);

    EndorsementReferenceValue {
        endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
        required_claims: Some(ClaimReferenceValue { claim_types: vec![] }),
        rekor: Some(rekor),
        ..Default::default()
    }
}

/// Creates a `VerifyingKey` instance from a PEM key.
pub fn create_verifying_key_from_pem(public_key_pem: &str, key_id: u32) -> VerifyingKey {
    let public_key_raw = convert_pem_to_raw(public_key_pem).expect("failed to convert key");
    VerifyingKey { r#type: KeyType::EcdsaP256Sha256.into(), key_id, raw: public_key_raw }
}

/// Creates a `VerifyingKey` instance from a raw key.
pub fn create_verifying_key_from_raw(public_key_raw: &[u8], key_id: u32) -> VerifyingKey {
    VerifyingKey { r#type: KeyType::EcdsaP256Sha256.into(), key_id, raw: public_key_raw.to_vec() }
}

/// Creates a `VerifyingKeyReferenceValue` instance from a key set.
pub fn create_verifying_key_reference_value(
    key_set: Option<VerifyingKeySet>,
) -> VerifyingKeyReferenceValue {
    VerifyingKeyReferenceValue {
        r#type: {
            match key_set {
                Some(ks) => Some(verifying_key_reference_value::Type::Verify(ks)),
                None => Some(verifying_key_reference_value::Type::Skip(SkipVerification {})),
            }
        },
    }
}

/// Creates an `EndorsementReferenceValue` instance from ingredients.
pub fn create_endorsement_reference_value_from_raw(
    endorser_public_key: &[u8],
    key_id: u32,
    rekor_public_key: &[u8],
) -> EndorsementReferenceValue {
    let endorser_key = create_verifying_key_from_raw(endorser_public_key, key_id);
    let rekor_key = create_verifying_key_from_raw(rekor_public_key, 1);
    create_endorsement_reference_value(endorser_key, Some(rekor_key))
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
///     for the verification. The deprecated fields `endorser_public_key` and
///     `rekor_public_key` will be ignored.
pub fn verify_endorsement(
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
    let current_time = Instant::from_unix_millis(now_utc_millis);
    let claims: Vec<&str> = required_claims.claim_types.iter().map(|x| &**x).collect();
    statement.validate(None, current_time, &claims).context("validating endorsement statement")?;

    let rekor_ref_value =
        ref_value.rekor.as_ref().context("no rekor key set in signed endorsement")?;
    match rekor_ref_value.r#type.as_ref() {
        Some(verifying_key_reference_value::Type::Skip(_)) => Ok(statement),
        Some(verifying_key_reference_value::Type::Verify(key_set)) => {
            let log_entry = &signed_endorsement.rekor_log_entry;
            if log_entry.is_empty() {
                anyhow::bail!("log entry unavailable but verification was requested");
            }
            let log_entry =
                verify_rekor_log_entry(log_entry, key_set, &endorsement.serialized, now_utc_millis)
                    .context("verifying Rekor log entry")?;
            compare_endorser_public_key(&log_entry, signature.key_id, endorser_key_set)?;
            Ok(statement)
        }
        None => Err(anyhow::anyhow!("empty Rekor verifying key set reference value")),
    }
}

/// Compares `public_key` against a particular verifying key in the set.
fn compare_endorser_public_key(
    log_entry: &LogEntry,
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
        KeyType::EcdsaP256Sha256 => log_entry.compare_public_key(&key.raw),
    }
}

pub fn is_firmware_type(statement: &DefaultStatement) -> bool {
    statement.predicate.claims.iter().any(|x| x.r#type == FIRMWARE_CLAIM_TYPE)
}

pub fn is_kernel_type(statement: &DefaultStatement) -> bool {
    statement.predicate.claims.iter().any(|x| x.r#type == KERNEL_CLAIM_TYPE)
}
