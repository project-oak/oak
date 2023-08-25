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
    AttestationVerificationOptions, LayerVerificationOptions, TransparencyVerificationOptions,
};
use alloc::{boxed::Box, collections::BTreeMap, string::String, vec::Vec};
use oak_remote_attestation::proto::oak::session::v1::{
    AttestationEndorsement, AttestationEvidence, BinaryAttestation,
};

use crate::rekor::{get_rekor_log_entry_body, verify_rekor_log_entry};
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_transparency_claims::claims::{parse_endorsement_statement, validate_endorsement};

/// Reference values used by the verifier to appraise the attestation evidence.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-reference-values>
pub struct ReferenceValue {
    pub binary_hash: Vec<u8>,
}

/// A trait implementing the functionality of a verifier that appraises the attestation evidence and
/// produces an attestation result.
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-verifier>
pub trait AttestationVerifier: Send + Sync {
    /// Verify that the provided evidence was endorsed and contains specified reference values.
    fn verify(
        &self,
        evidence: &AttestationEvidence,
        endorsement: &AttestationEndorsement,
        reference_value: &ReferenceValue,
    ) -> anyhow::Result<()>;
}

/// An instance of [`AttestationVerifier`] that succeeds iff the provided attestation is empty.
///
/// Useful when no attestation is expected to be generated by the other side of a remotely
/// attested connection.
pub struct InsecureAttestationVerifier;

impl AttestationVerifier for InsecureAttestationVerifier {
    fn verify(
        &self,
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

/// An AttestationVerifier that can be configured using an AttestationVerificationOptions object.
pub struct ConfigurableAttestationVerifier {
    verifiers: Vec<Box<dyn AttestationVerifier>>,
    layer_verifiers: BTreeMap<String, Box<AttestationLayerVerifier>>,
    default_layer_verifier: Option<Box<AttestationLayerVerifier>>,
}

impl ConfigurableAttestationVerifier {
    pub fn create(opts: &AttestationVerificationOptions) -> ConfigurableAttestationVerifier {
        // TODO(#3641): Add more verifiers based on the config, and once #4074 is completed.
        let default_layer_verifier = opts
            .default_layer_verification_option
            .as_ref()
            .map(|opt| Box::new(AttestationLayerVerifier::create(opt)));
        Self {
            verifiers: Vec::new(),
            layer_verifiers: BTreeMap::new(),
            default_layer_verifier,
        }
    }
}

impl AttestationVerifier for ConfigurableAttestationVerifier {
    fn verify(
        &self,
        evidence: &AttestationEvidence,
        endorsement: &AttestationEndorsement,
        reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        for verifier in &self.verifiers {
            verifier.verify(evidence, endorsement, reference_value)?;
        }
        // TODO(#3641): Update accordingly once #4074 is completed.
        for verifier in self.layer_verifiers.values() {
            verifier.verify(evidence, endorsement, reference_value)?;
        }
        //  TODO(#3641): Run the following only for layers not in `layer_verifiers`.
        if let Some(verifier) = &self.default_layer_verifier {
            verifier.verify(evidence, endorsement, reference_value)?;
        }
        Ok(())
    }
}

/// Verification logic for verifying evidence from a single DICE layer. This verifier can be
/// configured using an instance of LayerVerificationOptions.
pub struct AttestationLayerVerifier {
    verifiers: Vec<Box<dyn AttestationVerifier>>,
    binary_verifiers: BTreeMap<String, Vec<Box<dyn AttestationVerifier>>>,
    default_binary_verifier: Option<Vec<Box<dyn AttestationVerifier>>>,
}

impl AttestationLayerVerifier {
    pub fn create(opts: &LayerVerificationOptions) -> AttestationLayerVerifier {
        let default_binary_verifier = opts
            .default_transparency_verification_options
            .as_ref()
            .map(create_transparency_verifier);
        Self {
            verifiers: Vec::new(),
            binary_verifiers: BTreeMap::new(),
            default_binary_verifier,
        }
    }
}

impl AttestationVerifier for AttestationLayerVerifier {
    fn verify(
        &self,
        evidence: &AttestationEvidence,
        endorsement: &AttestationEndorsement,
        reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        for verifier in &self.verifiers {
            verifier.verify(evidence, endorsement, reference_value)?;
        }
        // TODO(#3641): Update accordingly once #4074 is completed.
        for verifiers in self.binary_verifiers.values() {
            for verifier in verifiers {
                verifier.verify(evidence, endorsement, reference_value)?;
            }
        }
        //  TODO(#3641): Run the following for binaries not specified in `binary_verifiers`.
        if let Some(verifiers) = &self.default_binary_verifier {
            for verifier in verifiers {
                verifier.verify(evidence, endorsement, reference_value)?;
            }
        }
        Ok(())
    }
}

pub fn create_transparency_verifier(
    opts: &TransparencyVerificationOptions,
) -> Vec<Box<dyn AttestationVerifier>> {
    let mut verifiers: Vec<Box<dyn AttestationVerifier>> = Vec::new();
    verifiers.push(Box::new(EndorsementStatementVerifier {}));
    if let Some(VerificationData(data)) = &opts.rekor_entry_verification {
        verifiers.push(Box::new(RekorLogEntryVerifier {
            base64_pem_encoded_rekor_public_key: data.base64_pem_encoded_rekor_public_key.clone(),
            base64_pem_encoded_endorser_public_key: data
                .base64_pem_encoded_endorser_public_key
                .clone(),
        }))
    }
    verifiers
}

/// AttestationVerifier for verifying the content of an endorsement statement and checking that it
/// has the same subject as the measurement.
pub struct EndorsementStatementVerifier {
    // TODO(#3641): Additional info may be required here to correctly extract the binary digest from
// the given evidence.
}

impl AttestationVerifier for EndorsementStatementVerifier {
    fn verify(
        &self,
        evidence: &AttestationEvidence,
        endorsement: &AttestationEndorsement,
        _reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        if let Some(binary_attestation) = &endorsement.binary_attestation {
            verify_endorsement_statement(
                &binary_attestation.endorsement_statement,
                &get_binary_digest(evidence),
            )?;
        }
        Ok(())
    }
}

fn get_binary_digest(_evidence: &AttestationEvidence) -> Vec<u8> {
    // TODO(#3641): Extract the actual binary digest from the evidence.
    Vec::new()
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
    if claim.subject.len() != 1 {
        anyhow::bail!(
            "expected 1 subject in the endorsement, found {}",
            claim.subject.len()
        );
    }

    // TODO(#3641): Require that binary digest is not empty.
    if !binary_digest.is_empty() {
        let binary_digest = core::str::from_utf8(binary_digest)?;
        if claim.subject[0].digest["sha256"] != binary_digest {
            anyhow::bail!(
                "unexpected binary SHA256 digest: expected {binary_digest}, got {}",
                claim.subject[0].digest["sha256"]
            );
        }
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

pub struct RekorLogEntryVerifier {
    base64_pem_encoded_rekor_public_key: String,
    base64_pem_encoded_endorser_public_key: String,
}

impl AttestationVerifier for RekorLogEntryVerifier {
    fn verify(
        &self,
        _evidence: &AttestationEvidence,
        endorsement: &AttestationEndorsement,
        _reference_value: &ReferenceValue,
    ) -> anyhow::Result<()> {
        if let Some(binary_attestation) = &endorsement.binary_attestation {
            let rekor_public_key_bytes =
                BASE64_STANDARD.decode(&binary_attestation.base64_pem_encoded_rekor_public_key)?;
            verify_rekor_log_entry(
                &binary_attestation.rekor_log_entry,
                &rekor_public_key_bytes,
                &binary_attestation.endorsement_statement,
            )?;
            verify_rekor_public_key(
                binary_attestation,
                &self.base64_pem_encoded_rekor_public_key,
            )?;
            verify_endorser_public_key(
                binary_attestation,
                &self.base64_pem_encoded_endorser_public_key,
            )?;
        }
        Ok(())
    }
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
