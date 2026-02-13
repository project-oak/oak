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

//! Provides verification based on evidence, endorsements and reference values.

use alloc::{format, string::ToString, sync::Arc, vec};

use anyhow::Context;
use coset::{CborSerializable, CoseKey, cwt::ClaimsSet};
use ecdsa::{Signature, signature::Verifier};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_dice::cert::{cose_key_to_verifying_key, get_public_key_from_claims_set};
use oak_proto_rust::oak::attestation::v1::{
    AttestationResults, Endorsements, EventAttestationResults, EventLog, Evidence, ExpectedValues,
    ExtractedEvidence, LayerEvidence, ReferenceValues, attestation_results::Status, endorsements,
    expected_values,
};
use oak_time::{Clock, Instant};
use p256::ecdsa::VerifyingKey;

use crate::{
    compare::compare_expected_values,
    expect::get_expected_values,
    extract::{EventIdType, claims_set_from_serialized_cert, extract_event_data, extract_evidence},
    platform::verify_root_attestation_signature,
    results::set_user_data_payload,
};

// We don't use additional authenticated data.
const ADDITIONAL_DATA: &[u8] = b"";

pub fn to_attestation_results(
    verify_result: &anyhow::Result<ExtractedEvidence>,
) -> AttestationResults {
    match verify_result {
        #[allow(deprecated)]
        Ok(extracted_evidence) => AttestationResults {
            status: Status::Success.into(),
            encryption_public_key: extracted_evidence.encryption_public_key.clone(),
            signing_public_key: extracted_evidence.signing_public_key.clone(),
            extracted_evidence: Some(extracted_evidence.clone()),
            ..Default::default()
        },
        Err(err) => AttestationResults {
            status: Status::GenericFailure.into(),
            reason: format!("{:#?}", err),
            ..Default::default()
        },
    }
}

// TODO: b/437347371 - To be moved out of the Oak repo.
// NB: All attestation verifiers belong in verifiers.rs, not here, but we
// didn't bother to move it since it goes away anyway.
pub struct SoftwareRootedDiceAttestationVerifier {
    clock: Arc<dyn Clock>,
}

impl SoftwareRootedDiceAttestationVerifier {
    pub fn new(clock: Arc<dyn Clock>) -> Self {
        Self { clock }
    }
}

impl AttestationVerifier for SoftwareRootedDiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        _endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        // Get current time.
        let _ = self.clock.get_time();

        // Verify DICE chain integrity.
        // The output argument is ommited because last layer's certificate authority key
        // is not used to sign anything.
        let _ = verify_software_rooted_dice_chain(evidence).context("verifying DICE chain")?;

        // TODO: b/366419879 - Combine per-event attestation results.
        #[allow(deprecated)]
        Ok(AttestationResults {
            status: Status::Success.into(),
            reason: "".to_string(),
            encryption_public_key: vec![],
            signing_public_key: vec![],
            extracted_evidence: None,
            event_attestation_results: vec![],
        })
    }
}

/// Verifies signatures of the certificates in the DICE chain and returns last
/// layer's Certificate Authority key if the verification is successful.
pub fn verify_software_rooted_dice_chain(evidence: &Evidence) -> anyhow::Result<VerifyingKey> {
    let root_layer_verifying_key = {
        let first_layer_option = evidence.layers.first();
        let first_layer =
            first_layer_option.ok_or_else(|| anyhow::anyhow!("no first layer evidence"))?;
        let cert = coset::CoseSign1::from_slice(&first_layer.eca_certificate)
            .map_err(|_cose_err| anyhow::anyhow!("couldn't parse certificate"))?;
        let payload = cert.payload.ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
        let claims = ClaimsSet::from_slice(&payload)
            .map_err(|_cose_err| anyhow::anyhow!("couldn't parse claims set"))?;
        let cose_key = get_public_key_from_claims_set(&claims)
            .map_err(|msg| anyhow::anyhow!(msg))
            .context("getting public key from claims")?;
        cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))?
    };

    // Sequentially verify the layers, eventually retrieving the verifying key of
    // the last layer.
    let last_layer_verifying_key = evidence
        .layers
        .iter()
        .try_fold(root_layer_verifying_key, |previous_layer_verifying_key, current_layer| {
            let cert = coset::CoseSign1::from_slice(&current_layer.eca_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("couldn't parse certificate"))?;
            cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                previous_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
            let payload = cert.payload.ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
            let claims = ClaimsSet::from_slice(&payload)
                .map_err(|_cose_err| anyhow::anyhow!("couldn't parse claims set"))?;
            let cose_key = get_public_key_from_claims_set(&claims)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("getting public key from claims")?;
            cose_key_to_verifying_key(&cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("converting COSE key")
        })
        .context("verifying DICE chain")?;

    // Verify the event log claim for this layer if it exists. This is done for all
    // layers here, since the event log is tied uniquely closely to the DICE chain.
    if let Some(event_log) = &evidence.event_log {
        let layers_to_check = if evidence.layers.is_empty() {
            &evidence.layers
        } else {
            &evidence.layers[1..] // Slice from the second element (index 1) to
            // the end
        };
        validate_that_event_log_is_captured_in_dice_layers(
            event_log,
            layers_to_check,
            EventLogType::OriginalEventLog.into(),
        )
        .context("validating that event log is captured in DICE layers")?
    } else {
        anyhow::bail!("event log is not present in the evidence");
    }

    Ok(last_layer_verifying_key)
}

/// Verifies entire setup by forwarding to individual setup types.
///
/// This just fetches expected values using [`expect::get_expected_values`],
/// and then call [`verify_with_expected_values`] providing those values.
///
/// If you'd like to cache and reuse the values, call those two methods
/// independently, and cache the results of the first.
pub fn verify(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<ExtractedEvidence> {
    let expected_values = get_expected_values(now_utc_millis, endorsements, reference_values)
        .context("getting expected values")?;

    verify_with_expected_values(now_utc_millis, evidence, endorsements, &expected_values)
        .context("verifying expected values")
}

/// Verifies entire setup by forwarding to individual setup types.
pub fn verify_with_expected_values(
    now_utc_millis: i64,
    evidence: &Evidence,
    endorsements: &Endorsements,
    expected_values: &ExpectedValues,
) -> anyhow::Result<ExtractedEvidence> {
    // Ensure the Attestation report is properly signed by the platform and that it
    // includes the root public key used in the DICE chain.
    {
        let tee_certificate: &[u8] =
            match endorsements.r#type.as_ref().context("no endorsements")? {
                endorsements::Type::OakRestrictedKernel(endorsements) => endorsements
                    .root_layer
                    .as_ref()
                    .context("no root layer endorsements")?
                    .tee_certificate
                    .as_ref(),
                endorsements::Type::OakContainers(endorsements) => endorsements
                    .root_layer
                    .as_ref()
                    .context("no root layer endorsements")?
                    .tee_certificate
                    .as_ref(),
                endorsements::Type::Cb(endorsements) => endorsements
                    .root_layer
                    .as_ref()
                    .context("no root layer endorsements")?
                    .tee_certificate
                    .as_ref(),
            };
        let amd_expected_values =
            match expected_values.r#type.as_ref().context("no expected values")? {
                expected_values::Type::OakRestrictedKernel(expected_values) => expected_values
                    .root_layer
                    .as_ref()
                    .context("no root layer expected values")?
                    .amd_sev
                    .as_ref(),
                expected_values::Type::OakContainers(expected_values) => expected_values
                    .root_layer
                    .as_ref()
                    .context("no root layer expected values")?
                    .amd_sev
                    .as_ref(),
                expected_values::Type::Cb(expected_values) => expected_values
                    .root_layer
                    .as_ref()
                    .context("no root layer expected values")?
                    .amd_sev
                    .as_ref(),
            };
        let check_vcek_cert_expiry =
            amd_expected_values.map(|value| value.check_vcek_cert_expiry).unwrap_or(false);
        let root_layer = evidence.root_layer.as_ref().context("no root layer evidence")?;
        verify_root_attestation_signature(
            Instant::from_unix_millis(now_utc_millis),
            check_vcek_cert_expiry,
            root_layer,
            tee_certificate,
        )
        .context("verifying root signature")?;
    };

    // Ensure the DICE chain signatures are valid and extract the measurements,
    // public keys and other attestation-related data from the DICE chain.
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(evidence).context("verifying DICE chain")?;

    compare_expected_values(&extracted_evidence, expected_values)
        .context("comparing expected values to evidence")?;

    Ok(extracted_evidence)
}

// The type of event log in the attestation evidence to verify.
pub enum EventLogType {
    // The original `event_log` in the attestation evidence.
    OriginalEventLog,
    // The `transparent_event_log`, populated with event entries that do not contain sensitive
    // data.
    TransparentEventLog,
}

/// Verifies signatures of the certificates in the DICE chain and returns last
/// layer's Certificate Authority key if the verification is successful.
pub fn verify_dice_chain(
    evidence: &Evidence,
    event_log_type: EventLogType,
) -> anyhow::Result<VerifyingKey> {
    let root_layer_verifying_key = {
        let cose_key = {
            let root_layer = evidence
                .root_layer
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
            CoseKey::from_slice(&root_layer.eca_public_key).map_err(|_cose_err| {
                anyhow::anyhow!("couldn't deserialize root layer public key")
            })?
        };
        cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))?
    };

    // Sequentially verify the layers, eventually retrieving the verifying key of
    // the last layer.
    let last_layer_verifying_key = evidence
        .layers
        .iter()
        .try_fold(root_layer_verifying_key, |previous_layer_verifying_key, current_layer| {
            let cert = coset::CoseSign1::from_slice(&current_layer.eca_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("couldn't parse certificate"))?;
            cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                previous_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
            let payload = cert.payload.ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
            let claims = ClaimsSet::from_slice(&payload)
                .map_err(|_cose_err| anyhow::anyhow!("couldn't parse claims set"))?;
            let cose_key = get_public_key_from_claims_set(&claims)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("getting public key from claims")?;
            cose_key_to_verifying_key(&cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("converting COSE key")
        })
        .context("verifying DICE chain")?;

    match event_log_type {
        EventLogType::OriginalEventLog => {
            // Verify the event log claim for this layer if it exists. This is done for all
            // layers here, since the event log is tied uniquely closely to the DICE chain.
            if let Some(event_log) = &evidence.event_log {
                validate_that_event_log_is_captured_in_dice_layers(
                    event_log,
                    &evidence.layers,
                    event_log_type.into(),
                )
                .context("validating that event log is captured in DICE layers")?
            } else {
                anyhow::bail!("event log is not present in the evidence");
            }
        }
        EventLogType::TransparentEventLog => {
            if let Some(transparent_event_log) = &evidence.transparent_event_log {
                validate_that_event_log_is_captured_in_dice_layers(
                    transparent_event_log,
                    &evidence.layers,
                    event_log_type.into(),
                )
                .context("validating that event log is captured in DICE layers")?
            } else {
                anyhow::bail!("transparent event log is not present in the evidence");
            }
        }
    }

    Ok(last_layer_verifying_key)
}

/// Verifies signatures of the certificates in the DICE chain and extracts the
/// evidence values from the certificates if the verification is successful.
// TODO: b/356631464 - Remove this function once all clients use verification
// policies.
pub fn verify_dice_chain_and_extract_evidence(
    evidence: &Evidence,
) -> anyhow::Result<ExtractedEvidence> {
    let root_layer_verifying_key = {
        let cose_key = {
            let root_layer = evidence
                .root_layer
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("no root layer evidence"))?;
            CoseKey::from_slice(&root_layer.eca_public_key).map_err(|_cose_err| {
                anyhow::anyhow!("couldn't deserialize root layer public key")
            })?
        };
        cose_key_to_verifying_key(&cose_key).map_err(|msg| anyhow::anyhow!(msg))?
    };

    // Sequentially verify the layers, eventually retrieving the verifying key of
    // the last layer.
    let last_layer_verifying_key = evidence
        .layers
        .iter()
        .try_fold(root_layer_verifying_key, |previous_layer_verifying_key, current_layer| {
            let cert = coset::CoseSign1::from_slice(&current_layer.eca_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse certificate"))?;
            cert.verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                previous_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
            let payload = cert.payload.ok_or_else(|| anyhow::anyhow!("no cert payload"))?;
            let claims = ClaimsSet::from_slice(&payload)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
            let cose_key = get_public_key_from_claims_set(&claims)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("getting public key from claims")?;
            cose_key_to_verifying_key(&cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("converting COSE key")
        })
        .context("getting last layer key")?;

    // Use the last layer's verification key to verify the application keys.
    {
        let appl_keys = evidence
            .application_keys
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no application keys in evidence"))?;

        // Verify encryption certificate.
        let encryption_cert =
            coset::CoseSign1::from_slice(&appl_keys.encryption_public_key_certificate)
                .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
        encryption_cert
            .verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                last_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))
            .context("verifying CWT signature")?;

        // Verify signing certificate.
        let signing_cert = coset::CoseSign1::from_slice(&appl_keys.signing_public_key_certificate)
            .map_err(|_cose_err| anyhow::anyhow!("could not parse encryption certificate"))?;
        signing_cert
            .verify_signature(ADDITIONAL_DATA, |signature, contents| {
                let sig = Signature::from_slice(signature)?;
                last_layer_verifying_key.verify(contents, &sig)
            })
            .map_err(|error| anyhow::anyhow!(error))?;
    }

    // Verify the event log claim for this layer if it exists. This is done for all
    // layers here, since the event log is tied uniquely closely to the DICE chain.
    if let Some(event_log) = &evidence.event_log {
        validate_that_event_log_is_captured_in_dice_layers(
            event_log,
            &evidence.layers,
            EventLogType::OriginalEventLog.into(),
        )
        .context("validating that event log is captured in DICE layers")?
    }
    extract_evidence(evidence)
}

/// Verifies the signed user data certificate and returns an
/// [`EventAttestationResults`] containing the payload bytes.
///
/// Parses the provided `signed_user_data_certificate` bytes as a COSE_Sign1
/// structure, verifies its signature using the given `verifying_key`, and
/// returns the payload as an `EventAttestationResults` with the
/// `user-data-payload` artifact key.
pub fn verify_user_data_certificate(
    signed_user_data_certificate: &[u8],
    verifying_key: &VerifyingKey,
) -> anyhow::Result<EventAttestationResults> {
    // Parse the signed user data certificate as a COSE_Sign1 structure.
    let user_data_cert = coset::CoseSign1::from_slice(signed_user_data_certificate)
        .map_err(|_cose_err| anyhow::anyhow!("could not parse signed user data certificate"))?;

    // Verify the signature using the provided verification key.
    user_data_cert
        .verify_signature(ADDITIONAL_DATA, |signature, contents| {
            let sig = Signature::from_slice(signature)?;
            verifying_key.verify(contents, &sig)
        })
        .map_err(|error| anyhow::anyhow!(error))
        .context("verifying signed user data certificate signature")?;

    // Extract the payload bytes and wrap in an EventAttestationResults.
    let payload = user_data_cert
        .payload
        .ok_or_else(|| anyhow::anyhow!("no payload in signed user data certificate"))?;
    let mut results = EventAttestationResults::default();
    set_user_data_payload(&mut results, &payload);
    Ok(results)
}

/// Validates that the digest of the events captured in the event log are
/// correctly described in the claims of the associated dice layers.
// Claim entries are under different keys for standard events and transparent
// events, so the caller must also pass the EventIdType to find the appropriate
// claims for the events.
fn validate_that_event_log_is_captured_in_dice_layers(
    event_log: &EventLog,
    dice_layers: &[LayerEvidence],
    event_id_type: EventIdType,
) -> anyhow::Result<()> {
    dice_layers.iter().zip(event_log.encoded_events.iter()).try_for_each(
        |(current_layer, encoded_event)| {
            let event_digest = {
                let claims = claims_set_from_serialized_cert(&current_layer.eca_certificate)
                    .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
                extract_event_data(&claims, &event_id_type)
                    .context("extracting event data")?
                    .event
                    .context("missing event")?
            };
            let actual_event_hash = &<sha2::Sha256 as sha2::Digest>::digest(encoded_event).to_vec();
            if actual_event_hash != &event_digest.sha2_256 {
                Err(anyhow::anyhow!("event log hash mismatch"))
            } else {
                Ok(())
            }
        },
    )
}

#[cfg(test)]
mod tests;
