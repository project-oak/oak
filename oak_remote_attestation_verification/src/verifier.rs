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

use crate::proto::oak::verification::v1::{
    transparency_verification_options::RekorEntryVerification::VerificationData,
    TransparencyVerificationOptions,
};
use alloc::vec::Vec;
use oak_remote_attestation::proto::oak::session::v1::{
    AttestationEndorsement, AttestationEvidence, BinaryAttestation,
};

use crate::rekor::{get_rekor_log_entry_body, verify_rekor_log_entry};
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_transparency_claims::claims::{
    parse_endorsement_statement, validate_endorsement, verify_validity_duration,
};

/// Reference values used by the verifier to appraise the attestation evidence.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
pub struct ReferenceValue {
    pub binary_hash: Vec<u8>,
}

/// A trait implementing the functionality of a verifier that appraises the attestation evidence and
/// produces an attestation result.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-verifier>
pub trait AttestationVerifier: Clone + Send + Sync {
    /// Verify that the provided evidence was endorsed and contains specified reference values.
    fn verify(
        evidence: &AttestationEvidence,
        endorsement: &AttestationEndorsement,
        reference_value: &ReferenceValue,
    ) -> anyhow::Result<()>;
}

/// An instance of [`AttestationVerifier`] that succeeds iff the provided attestation is empty.
///
/// Useful when no attestation is expected to be generated by the other side of a remotely
/// attested connection.
#[derive(Clone)]
pub struct InsecureAttestationVerifier;

impl AttestationVerifier for InsecureAttestationVerifier {
    fn verify(
        evidence: &AttestationEvidence,
        _endorsement: &AttestationEndorsement,
        _reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        // We check that the attestation report is empty in order to avoid accidentally ignoring a
        // real attestation from the other side, although in principle a more lenient
        // implementation of this struct could be used that always ignores also non-empty
        // attestations.
        if evidence.attestation.is_empty() {
            Ok(())
        } else {
            Err(anyhow::anyhow!(
                "expected empty attestation report, got {:?}",
                evidence.attestation
            ))
        }
    }
}

/// Verifies the transparent release endorsement for a given measurement (which must be a SHA256
/// digest), using the given verification options to control the extent of the verification.
/// Summary of the verification logic:
///
/// 1. Verifies that the endorsement statement in the given `BinaryAttestation` instance contains a
/// single subject with a SHA256 digest equal to `measurement_from_evidence`.
/// 1. If the input `TransparencyVerificationOptions` requires Rekor log verification:
///     1. verifies that the `BinaryAttestation` contains a valid Rekor log entry (see
/// `verify_rekor_log_entry` for details.),
///     1. verifies the Rekor public key in `BinaryAttestation` against the Rekor public key in
/// `TransparencyVerificationOptions`,
///     1. verifies the endorser public key included in the Rekor
/// log entry against the endorser public key in `TransparencyVerificationOptions`.
pub fn verify_transparent_release_endorsement(
    measurement_from_evidence: &[u8],
    binary_attestation: &BinaryAttestation,
    opts: &TransparencyVerificationOptions,
) -> anyhow::Result<()> {
    verify_endorsement_statement(
        &binary_attestation.endorsement_statement,
        measurement_from_evidence,
    )?;

    if let Some(VerificationData(data)) = &opts.rekor_entry_verification {
        let base64_pem_encoded_rekor_public_key = data.base64_pem_encoded_rekor_public_key.clone();
        let base64_pem_encoded_endorser_public_key =
            data.base64_pem_encoded_endorser_public_key.clone();
        let rekor_public_key_bytes =
            BASE64_STANDARD.decode(&base64_pem_encoded_rekor_public_key)?;

        verify_rekor_log_entry(
            &binary_attestation.rekor_log_entry,
            &rekor_public_key_bytes,
            &binary_attestation.endorsement_statement,
        )?;
        verify_rekor_public_key(binary_attestation, &base64_pem_encoded_rekor_public_key)?;
        verify_endorser_public_key(binary_attestation, &base64_pem_encoded_endorser_public_key)?;
    }

    Ok(())
}

/// Parses the given bytes into an endorsement statement and verifies it against the given Reference
/// values.
pub fn verify_endorsement_statement(
    endorsement_bytes: &[u8],
    binary_digest: &[u8],
) -> anyhow::Result<()> {
    let claim = parse_endorsement_statement(endorsement_bytes)?;
    if let Err(err) = validate_endorsement(&claim) {
        anyhow::bail!("validating endorsement: {err:?}");
    }
    verify_validity_duration(&claim)?;
    if claim.subject.len() != 1 {
        anyhow::bail!(
            "expected 1 subject in the endorsement, found {}",
            claim.subject.len()
        );
    }

    let binary_digest = core::str::from_utf8(binary_digest)?;
    if claim.subject[0].digest["sha256"] != binary_digest {
        anyhow::bail!(
            "unexpected binary SHA256 digest: expected {binary_digest}, got {}",
            claim.subject[0].digest["sha256"]
        );
    }

    Ok(())
}

/// Verifies that the rekor public key in the given BinaryAttestation is either the same as the
/// given public key, signed by it, or derived from it.
fn verify_rekor_public_key(
    binary_attestation: &BinaryAttestation,
    base64_pem_encoded_rekor_public_key: &str,
) -> anyhow::Result<()> {
    // TODO(#4231): Currently, we only check that the public keys are the same. Once Rekor starts
    // using rolling keys, the verification logic will have to be updated.
    if binary_attestation.base64_pem_encoded_rekor_public_key != base64_pem_encoded_rekor_public_key
    {
        anyhow::bail!("Rekor public key verification failed: expected {base64_pem_encoded_rekor_public_key}, got {}", 
        binary_attestation.base64_pem_encoded_rekor_public_key);
    }

    Ok(())
}

/// Verifies that the endorser's public key in the Rekor log entry in the given BinaryAttestation is
/// either the same as the given public key, signed by it, or derived from it.
fn verify_endorser_public_key(
    binary_attestation: &BinaryAttestation,
    base64_pem_encoded_endorser_public_key: &str,
) -> anyhow::Result<()> {
    let body = get_rekor_log_entry_body(&binary_attestation.rekor_log_entry)?;

    let endorser_public_key = body.spec.signature.public_key.content.clone();

    // TODO(#4231): Currently, we only check that the public keys are the same. Should be updated to
    // support verifying rolling keys.
    if endorser_public_key != base64_pem_encoded_endorser_public_key {
        anyhow::bail!(
            "endorser public key verification failed: expected {}, got {}",
            base64_pem_encoded_endorser_public_key,
            endorser_public_key
        );
    }

    Ok(())
}
