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

use alloc::{string::String, vec, vec::Vec};

use anyhow::Context;
use c2sp::{Policy, TLogProof};
use intoto::statement::{DefaultStatement, parse_statement};
use key_util::{convert_pem_to_raw, verify_signature};
use oak_proto_rust::oak::attestation::v1::{
    C2sptLogProofReferenceValue, ClaimReferenceValue, Endorsement, EndorsementReferenceValue,
    KeyType, Signature, SignedEndorsement, SkipVerification, VerifyingKey,
    VerifyingKeyReferenceValue, VerifyingKeySet, endorsement::Format,
    verifying_key_reference_value,
};
use oak_time::Instant;
use rekor::log_entry::{LogEntry, verify_rekor_log_entry};

/// No attempt will be made to decode the attachment of a firmware-type
/// binary unless this claim is present in the endorsement.
pub const FIRMWARE_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/10271.md";

/// No attempt will be made to decode the attachment of a kernel-type
/// binary unless this claim is present in the endorsement.
pub const KERNEL_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/98982.md";

/// Creates a `SignedEndorsement` from ingredients.
///
/// Arguments:
/// - serialized_endorsement: The actual endorsement as JSON.
/// - signature: The raw signature over the endorsement.
/// - key_id: The key ID for identifying the verifying key among several.
/// - subject: The endorsed subject, if needed for the verification. Optional
///   and empty in most cases.
/// - rekor_log_entry: The serialized Rekor log entry as JSON. Leave empty if
///   unavailable.
pub fn create_signed_endorsement(
    serialized_endorsement: &[u8],
    signature: &[u8],
    key_id: u32,
    subject: &[u8],
    log_entry: &[u8],
) -> SignedEndorsement {
    let endorsement = Endorsement {
        format: Format::EndorsementFormatJsonIntoto.into(),
        serialized: serialized_endorsement.to_vec(),
        subject: subject.to_vec(),
    };
    SignedEndorsement {
        endorsement: Some(endorsement),
        signature: Some(Signature { key_id, raw: signature.to_vec() }),
        rekor_log_entry: log_entry.to_vec(),
        ..Default::default()
    }
}

/// Creates an `EndorsementReferenceValue` from ingredients.
pub fn create_endorsement_reference_value(
    endorser_key: VerifyingKey,
    claim_types: Vec<String>,
    rekor_key: Option<VerifyingKey>,
) -> EndorsementReferenceValue {
    let rekor_key_set =
        rekor_key.map(|v| VerifyingKeySet { keys: [v].to_vec(), ..Default::default() });
    let rekor = create_verifying_key_reference_value(rekor_key_set);

    #[allow(deprecated)]
    EndorsementReferenceValue {
        endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
        required_claims: Some(ClaimReferenceValue { claim_types }),
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
    create_endorsement_reference_value(endorser_key, vec![], Some(rekor_key))
}

/// Verifies a signed endorsement against a reference value.
///
/// Returns the parsed statement whenever the verification succeeds, or an error
/// otherwise.
///
/// `now_utc_millis`: The current time in milliseconds UTC since Unix Epoch.
/// `signed_endorsement`: The endorsement along with signature and (optional)
///     any receipts from t-log like entities.
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

    if let Some(tlog) = ref_value.tlog.as_ref() {
        if let Some(rekor) = tlog.rekor.as_ref() {
            verify_rekor_log_entry(
                &signed_endorsement.rekor_log_entry,
                rekor,
                &endorsement.serialized,
                now_utc_millis,
            )
            .context("verifying Rekor log entry")?;
        }
        if let Some(c2sp) = tlog.c2sp.as_ref() {
            verify_c2sp_tlog_proof(signed_endorsement, endorsement, c2sp)
                .context("verifying C2SP tlog proof")?;
        }
    } else {
        #[allow(deprecated)]
        let rekor_ref_value =
            ref_value.rekor.as_ref().context("no rekor key set in signed endorsement")?;
        match rekor_ref_value.r#type.as_ref() {
            Some(verifying_key_reference_value::Type::Skip(_)) => {}
            Some(verifying_key_reference_value::Type::Verify(key_set)) => {
                let log_entry = &signed_endorsement.rekor_log_entry;
                if log_entry.is_empty() {
                    anyhow::bail!("log entry unavailable but verification was requested");
                }
                let log_entry = verify_rekor_log_entry(
                    log_entry,
                    key_set,
                    &endorsement.serialized,
                    now_utc_millis,
                )
                .context("verifying Rekor log entry")?;
                compare_endorser_public_key(&log_entry, signature.key_id, endorser_key_set)?;
            }
            None => anyhow::bail!("empty Rekor verifying key set reference value"),
        }
    }

    Ok(statement)
}

/// Verifies a C2SP tlog-proof bundle against the given endorsement and
/// reference value.
// TODO: b/485180287 - move some of this into the c2sp crate.
fn verify_c2sp_tlog_proof(
    signed_endorsement: &SignedEndorsement,
    endorsement: &Endorsement,
    c2sp_ref: &C2sptLogProofReferenceValue,
) -> anyhow::Result<()> {
    let proof_bytes = &signed_endorsement.c2sp_tlog_proof;
    if proof_bytes.is_empty() {
        anyhow::bail!("C2SP tlog proof unavailable but verification was requested");
    }
    let proof_text =
        core::str::from_utf8(proof_bytes).context("C2SP tlog proof is not valid UTF-8")?;
    let policy =
        Policy::parse(&c2sp_ref.policy).map_err(|e| anyhow::anyhow!("parsing policy: {e}"))?;
    let proof = TLogProof::parse(proof_text)
        .map_err(|e| anyhow::anyhow!("parsing C2SP tlog proof: {e}"))?;
    proof
        .verify(&policy, &endorsement.serialized)
        .map_err(|e| anyhow::anyhow!("verifying C2SP tlog proof: {e}"))?;
    Ok(())
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

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use base64::{Engine, engine::general_purpose::STANDARD as B64};
    use c2sp::{Checkpoint, NoteSigningKey, SignatureType};
    use oak_proto_rust::oak::attestation::v1::{
        C2sptLogProofReferenceValue, Endorsement, SignedEndorsement,
    };
    use oak_time::Instant;

    use super::*;

    /// Builds a complete proof without witness cosignatures.
    ///
    /// Returns `(proof_text, log_vkey_string)`.
    fn make_test_tlog_proof(
        entry: &[u8],
        origin: &str,
        log_key: &NoteSigningKey,
    ) -> (String, String) {
        use sha2::{Digest, Sha256};
        let root_hash: [u8; 32] =
            Sha256::new().chain_update([0x00]).chain_update(entry).finalize().into();
        let root_hash = oak_digest::Sha256::from(root_hash);
        let root_b64 = B64.encode(root_hash);
        let signed_payload = alloc::format!("{origin}\n1\n{root_b64}\n");
        let log_sig = log_key.sign(&signed_payload, Instant::UNIX_EPOCH);
        let checkpoint = Checkpoint {
            origin: origin.into(),
            tree_size: 1,
            root_hash,
            signed_payload,
            signatures: vec![log_sig],
        };
        let proof = TLogProof { index: 0, proof_hashes: vec![], checkpoint };
        let vkey = log_key.verifying_key.to_vkey_string();
        (proof.serialize(), vkey)
    }

    /// Builds a policy string with a log key and `quorum none`.
    fn make_log_policy(vkey: &str) -> String {
        alloc::format!("log {vkey}\nquorum none\n")
    }

    #[test]
    fn verify_c2sp_tlog_proof_succeeds() {
        let entry = b"test endorsement data";
        let origin = "test.log.example.com/log";
        let log_key = NoteSigningKey::from_parts(origin, SignatureType::Ed25519, [42u8; 32]);

        let (proof_text, vkey) = make_test_tlog_proof(entry, origin, &log_key);

        let signed_endorsement =
            SignedEndorsement { c2sp_tlog_proof: proof_text.into_bytes(), ..Default::default() };
        let endorsement = Endorsement { serialized: entry.to_vec(), ..Default::default() };
        let c2sp_ref = C2sptLogProofReferenceValue { policy: make_log_policy(&vkey) };

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_ok(), "expected success, got: {:?}", result.err());
    }

    #[test]
    fn verify_c2sp_tlog_proof_fails_when_proof_missing() {
        let origin = "test.log.example.com/log";
        let log_key = NoteSigningKey::from_parts(origin, SignatureType::Ed25519, [42u8; 32]);
        let vkey = log_key.verifying_key.to_vkey_string();
        let c2sp_ref = C2sptLogProofReferenceValue { policy: make_log_policy(&vkey) };
        let signed_endorsement = SignedEndorsement::default();
        let endorsement = Endorsement::default();

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("unavailable"), "unexpected error: {err}");
    }

    #[test]
    fn verify_c2sp_tlog_proof_fails_with_invalid_proof() {
        let origin = "test.log.example.com/log";
        let log_key = NoteSigningKey::from_parts(origin, SignatureType::Ed25519, [42u8; 32]);
        let vkey = log_key.verifying_key.to_vkey_string();

        let signed_endorsement = SignedEndorsement {
            c2sp_tlog_proof: b"not a valid proof".to_vec(),
            ..Default::default()
        };
        let endorsement = Endorsement::default();
        let c2sp_ref = C2sptLogProofReferenceValue { policy: make_log_policy(&vkey) };

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("parsing C2SP tlog proof"), "unexpected error: {err}");
    }

    #[test]
    fn verify_c2sp_tlog_proof_fails_with_wrong_entry() {
        let entry = b"correct endorsement data";
        let wrong_entry = b"wrong endorsement data";
        let origin = "test.log.example.com/log";
        let log_key = NoteSigningKey::from_parts(origin, SignatureType::Ed25519, [42u8; 32]);

        // Build a proof over the correct entry.
        let (proof_text, vkey) = make_test_tlog_proof(entry, origin, &log_key);

        let signed_endorsement =
            SignedEndorsement { c2sp_tlog_proof: proof_text.into_bytes(), ..Default::default() };
        // But pass the wrong entry as endorsement.serialized.
        let endorsement = Endorsement { serialized: wrong_entry.to_vec(), ..Default::default() };
        let c2sp_ref = C2sptLogProofReferenceValue { policy: make_log_policy(&vkey) };

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("verifying C2SP tlog proof"), "unexpected error: {err}");
    }

    #[test]
    fn verify_c2sp_tlog_proof_fails_with_wrong_key() {
        let entry = b"test endorsement data";
        let origin = "test.log.example.com/log";
        let log_key = NoteSigningKey::from_parts(origin, SignatureType::Ed25519, [42u8; 32]);
        let other_key = NoteSigningKey::from_parts(origin, SignatureType::Ed25519, [99u8; 32]);

        // Build a proof signed with log_key.
        let (proof_text, _vkey) = make_test_tlog_proof(entry, origin, &log_key);

        // But use other_key's vkey for verification.
        let wrong_vkey = other_key.verifying_key.to_vkey_string();

        let signed_endorsement =
            SignedEndorsement { c2sp_tlog_proof: proof_text.into_bytes(), ..Default::default() };
        let endorsement = Endorsement { serialized: entry.to_vec(), ..Default::default() };
        let c2sp_ref = C2sptLogProofReferenceValue { policy: make_log_policy(&wrong_vkey) };

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_err());
    }

    #[test]
    fn verify_c2sp_tlog_proof_succeeds_with_witness_policy() {
        let entry = b"test endorsement data";
        let log_origin = "test.log.example.com/log";
        let witness_origin = "test-witness.example.com";
        let log_key = NoteSigningKey::from_parts(log_origin, SignatureType::Ed25519, [42u8; 32]);
        let witness_key =
            NoteSigningKey::from_parts(witness_origin, SignatureType::CosignatureV1, [43u8; 32]);

        // Build the checkpoint, then sign it with both the log and a witness.
        use sha2::{Digest, Sha256};
        let root_hash: [u8; 32] =
            Sha256::new().chain_update([0x00]).chain_update(entry).finalize().into();
        let root_hash = oak_digest::Sha256::from(root_hash);
        let root_b64 = B64.encode(root_hash);
        let signed_payload = alloc::format!("{log_origin}\n1\n{root_b64}\n");
        let log_sig = log_key.sign(&signed_payload, Instant::UNIX_EPOCH);
        let cosig = witness_key.sign(&signed_payload, Instant::from_unix_seconds(1000));
        let checkpoint = Checkpoint {
            origin: log_origin.into(),
            tree_size: 1,
            root_hash,
            signed_payload,
            signatures: vec![log_sig, cosig],
        };
        let proof = TLogProof { index: 0, proof_hashes: vec![], checkpoint };
        let proof_text = proof.serialize();

        // Build a policy requiring this witness, including the log key.
        let log_vkey = log_key.verifying_key.to_vkey_string();
        let witness_vkey = witness_key.verifying_key.to_vkey_string();
        let policy_text = alloc::format!("log {log_vkey}\nwitness w1 {witness_vkey}\nquorum w1\n");

        let signed_endorsement =
            SignedEndorsement { c2sp_tlog_proof: proof_text.into_bytes(), ..Default::default() };
        let endorsement = Endorsement { serialized: entry.to_vec(), ..Default::default() };
        let c2sp_ref = C2sptLogProofReferenceValue { policy: policy_text };

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_ok(), "expected success, got: {:?}", result.err());
    }

    #[test]
    fn verify_c2sp_tlog_proof_fails_when_witness_policy_unsatisfied() {
        let entry = b"test endorsement data";
        let log_origin = "test.log.example.com/log";
        let witness_origin = "test-witness.example.com";
        let log_key = NoteSigningKey::from_parts(log_origin, SignatureType::Ed25519, [42u8; 32]);
        let witness_key =
            NoteSigningKey::from_parts(witness_origin, SignatureType::CosignatureV1, [43u8; 32]);

        // Build a proof without any witness cosignatures.
        let (proof_text, log_vkey) = make_test_tlog_proof(entry, log_origin, &log_key);

        // But the policy requires a witness.
        let witness_vkey = witness_key.verifying_key.to_vkey_string();
        let policy_text = alloc::format!("log {log_vkey}\nwitness w1 {witness_vkey}\nquorum w1\n");

        let signed_endorsement =
            SignedEndorsement { c2sp_tlog_proof: proof_text.into_bytes(), ..Default::default() };
        let endorsement = Endorsement { serialized: entry.to_vec(), ..Default::default() };
        let c2sp_ref = C2sptLogProofReferenceValue { policy: policy_text };

        let result = verify_c2sp_tlog_proof(&signed_endorsement, &endorsement, &c2sp_ref);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("verifying C2SP tlog proof"), "unexpected error: {err}");
    }
}
