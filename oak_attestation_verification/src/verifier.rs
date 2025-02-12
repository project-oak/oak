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

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};

use anyhow::Context;
use coset::{cwt::ClaimsSet, CborSerializable, CoseKey};
use ecdsa::{signature::Verifier, Signature};
use hashbrown::HashSet;
use itertools::izip;
use oak_attestation_verification_types::{
    policy::{EventPolicy, Policy},
    util::Clock,
    verifier::AttestationVerifier,
};
use oak_dice::cert::{cose_key_to_verifying_key, get_public_key_from_claims_set};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, endorsements, AttestationResults, Endorsements,
        EventAttestationResults, EventLog, Evidence, ExpectedValues, ExtractedEvidence,
        LayerEvidence, ReferenceValues,
    },
    Variant,
};
use oak_sev_snp_attestation_report::AttestationReport;
use p256::ecdsa::VerifyingKey;
use zerocopy::FromBytes;

use crate::{
    compare::compare_expected_values,
    expect::get_expected_values,
    extract::{claims_set_from_serialized_cert, extract_event_data, extract_evidence},
    platform::verify_root_attestation_signature,
    policy::platform::AmdSevSnpPolicy,
    util::hash_sha2_256,
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

pub struct AmdSevSnpDiceAttestationVerifier {
    platform_policy: AmdSevSnpPolicy,
    firmware_policy: Box<dyn EventPolicy>,
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Box<dyn Clock>,
}

impl AmdSevSnpDiceAttestationVerifier {
    pub fn new(
        platform_policy: AmdSevSnpPolicy,
        firmware_policy: Box<dyn EventPolicy>,
        event_policies: Vec<Box<dyn EventPolicy>>,
        clock: Box<dyn Clock>,
    ) -> Self {
        Self { platform_policy, firmware_policy, event_policies, clock }
    }
}

impl AttestationVerifier for AmdSevSnpDiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        // Get current time.
        let milliseconds_since_epoch = self.clock.get_milliseconds_since_epoch();

        // Get DICE root layer evidence.
        let root_layer = &evidence
            .root_layer
            .as_ref()
            .context("root DICE layer wasn't provided in the evidence")?;

        // Parse AMD SEV-SNP attestation report.
        let attestation_report = AttestationReport::ref_from(&root_layer.remote_attestation_report)
            .context("invalid AMD SEV-SNP attestation report")?;
        let firmware_measurement = &attestation_report.data.measurement;

        // Verify AMD SEV-SNP platform authenticity and configuration.
        let platform_endorsement = endorsements
            .platform
            .as_ref()
            .context("AMD SEV-SNP endorsement wasn't provided in endorsements")?;
        self.platform_policy
            .verify(attestation_report, platform_endorsement, milliseconds_since_epoch)
            .context("couldn't verify AMD SEV-SNP platform")?;

        // Verify that the DICE root ECA key is bound to the attestation report.
        verify_dice_root_eca_key(attestation_report, &root_layer.eca_public_key)
            .context("couldn't verify DICE root ECA key")?;

        // Verify DICE chain integrity.
        // The output argument is ommited because last layer's certificate authority key
        // is not used to sign anything.
        let _ = verify_dice_chain(evidence).context("couldn't verify DICE chain")?;

        // Verify firmware measurement.
        let firmware_endorsement = &endorsements
            .initial
            .as_ref()
            .context("firmware endorsement wasn't provided in endorsements")?;
        self.firmware_policy
            .verify(firmware_measurement, firmware_endorsement, milliseconds_since_epoch)
            .context("couldn't verify firmware")?;

        // Verify event log and event endorsements with corresponding policies.
        let event_log = &evidence
            .event_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("event log was not provided"))?;
        let event_endorsements = &endorsements.events;
        let event_attestation_results = verify_event_log(
            event_log,
            event_endorsements,
            self.event_policies.as_slice(),
            milliseconds_since_epoch,
        )
        .context("couldn't verify event log")?;

        verify_event_artifacts_uniqueness(&event_attestation_results)
            .context("couldn't verify event artifacts ID uniqueness")?;

        // TODO: b/366419879 - Combine per-event attestation results.
        #[allow(deprecated)]
        Ok(AttestationResults {
            status: Status::Unspecified.into(),
            reason: "".to_string(),
            encryption_public_key: vec![],
            signing_public_key: vec![],
            extracted_evidence: None,
            event_attestation_results,
        })
    }
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
        let root_layer = evidence.root_layer.as_ref().context("no root layer evidence")?;
        verify_root_attestation_signature(now_utc_millis, root_layer, tee_certificate)
            .context("verifying root signature")?;
    };

    // Ensure the DICE chain signatures are valid and extract the measurements,
    // public keys and other attestation-related data from the DICE chain.
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(evidence).context("invalid DICE chain")?;

    compare_expected_values(&extracted_evidence, expected_values)
        .context("comparing expected values to evidence")?;

    Ok(extracted_evidence)
}

/// Verifies that the root ECA public key of the DICE chain is bound to the
/// attestation report to ensure that the entire DICE chain is valid.
fn verify_dice_root_eca_key(
    attestation_report: &AttestationReport,
    eca_public_key: &[u8],
) -> anyhow::Result<()> {
    let expected = &hash_sha2_256(eca_public_key)[..];
    let actual = attestation_report.data.report_data;
    anyhow::ensure!(
        // The report data contains 64 bytes by default, but we only use the first 32 bytes
        // at the moment.
        expected.len() < actual.len() && expected == &actual[..expected.len()],
        "the root ECA public key is not bound to the AMD SEV-SNP attestation report"
    );
    Ok(())
}

/// Verifies signatures of the certificates in the DICE chain and returns last
/// layer's Certificate Authority key if the verification is successful.
pub fn verify_dice_chain(evidence: &Evidence) -> anyhow::Result<VerifyingKey> {
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
                .context("couldn't get a public key from claims")?;
            cose_key_to_verifying_key(&cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("couldn't convert cose key")
        })
        .context("couldn't verify DICE chain")?;

    // Verify the event log claim for this layer if it exists. This is done for all
    // layers here, since the event log is tied uniquely closely to the DICE chain.
    if let Some(event_log) = &evidence.event_log {
        validate_that_event_log_is_captured_in_dice_layers(event_log, &evidence.layers)
            .context("events in log do not match the digests in the dice chain")?
    } else {
        anyhow::bail!("event log is not present in the evidence");
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
                .context("getting pk from claims")?;
            cose_key_to_verifying_key(&cose_key)
                .map_err(|msg| anyhow::anyhow!(msg))
                .context("converting cose key")
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
            .context("failed to verify CWT signature")?;

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
        validate_that_event_log_is_captured_in_dice_layers(event_log, &evidence.layers)
            .context("events in log do not match the digests in the dice chain")?
    }
    extract_evidence(evidence)
}

/// Validates that the digest of the events captured in the event log are
/// correctly described in the claims of the associated dice layers.
fn validate_that_event_log_is_captured_in_dice_layers(
    event_log: &EventLog,
    dice_layers: &[LayerEvidence],
) -> anyhow::Result<()> {
    dice_layers.iter().zip(event_log.encoded_events.iter()).try_for_each(
        |(current_layer, encoded_event)| {
            let event_digest = {
                let claims = claims_set_from_serialized_cert(&current_layer.eca_certificate)
                    .map_err(|_cose_err| anyhow::anyhow!("could not parse claims set"))?;
                extract_event_data(&claims)
                    .context("couldn't extract event claim")?
                    .event
                    .context("Missing event")?
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

/// Verifies an Event Log using a combination of Event Policies.
///
/// Event Policies are provided as a list where each element corresponds to an
/// [`Event`] in the [`EventLog`] and [`EventEndorsement`] in the
/// [`EventEndorsements`] with the same index. This means that mapping between
/// Policies and Events is done via ordering.
fn verify_event_log(
    event_log: &EventLog,
    event_endorsements: &[Variant],
    policies: &[Box<dyn EventPolicy>],
    milliseconds_since_epoch: i64,
) -> anyhow::Result<Vec<EventAttestationResults>> {
    if policies.len() != event_log.encoded_events.len() {
        anyhow::bail!(
            "number of policies ({}) is not equal to the event log length ({})",
            policies.len(),
            event_log.encoded_events.len()
        );
    }
    if event_log.encoded_events.len() < event_endorsements.len() {
        anyhow::bail!(
            "event log length ({}) is smaller than the number of endorsements ({})",
            event_log.encoded_events.len(),
            event_endorsements.len()
        );
    }

    // Pad `event_endorsements` with an empty [`Variant`] to the same length as the
    // event log.
    let empty_endorsement = Variant::default();
    let mut padded_event_endorsements: Vec<&Variant> = event_endorsements.iter().collect();
    if event_log.encoded_events.len() > event_endorsements.len() {
        padded_event_endorsements.extend(
            core::iter::repeat(&empty_endorsement)
                .take(event_log.encoded_events.len() - event_endorsements.len()),
        );
    }

    let verification_iterator =
        izip!(policies.iter(), event_log.encoded_events.iter(), padded_event_endorsements.iter());
    let event_attestation_results = verification_iterator
        .map(|(event_policy, event, event_endorsement)| {
            event_policy.verify(event, event_endorsement, milliseconds_since_epoch).unwrap_or(
                // TODO: b/366186091 - Use Rust error types for failed attestation.
                EventAttestationResults { ..Default::default() },
            )
        })
        .collect::<Vec<EventAttestationResults>>();
    Ok(event_attestation_results)
}

/// Verifies that artifacts in all events have unique IDs.
fn verify_event_artifacts_uniqueness(
    event_attestation_results: &[EventAttestationResults],
) -> anyhow::Result<()> {
    event_attestation_results.iter().try_fold(HashSet::new(), |id_set, event| {
        let updated_id_set = event.artifacts.keys().try_fold(id_set, |mut global_id_set, id| {
            if global_id_set.insert(id) {
                Ok(global_id_set)
            } else {
                anyhow::bail!("artifact ID `{}` is duplicated in multiple events", id)
            }
        })?;
        Ok::<HashSet<&String>, anyhow::Error>(updated_id_set)
    })?;
    Ok(())
}

/// Returns a reference to the event artifact from `attestation_results` with a
/// given `artifact_id`.
pub fn get_event_artifact<'a>(
    attestation_results: &'a AttestationResults,
    artifact_id: &str,
) -> Option<&'a Vec<u8>> {
    attestation_results
        .event_attestation_results
        .iter()
        .find_map(|event| event.artifacts.get(artifact_id))
}

#[cfg(test)]
mod tests;
