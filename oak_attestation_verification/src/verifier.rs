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

use alloc::{boxed::Box, format};

use anyhow::Context;
use coset::{cwt::ClaimsSet, CborSerializable, CoseKey};
use ecdsa::{signature::Verifier, Signature};
use oak_attestation_verification_types::{
    policy::Policy, util::Clock, verifier::AttestationVerifier,
};
use oak_dice::cert::{cose_key_to_verifying_key, get_public_key_from_claims_set};
use oak_proto_rust::oak::attestation::v1::{
    attestation_results::Status, endorsements, AttestationResults, Endorsements, EventLog,
    Evidence, ExpectedValues, ExtractedEvidence, LayerEvidence, ReferenceValues,
};
use p256::ecdsa::VerifyingKey;

use crate::{
    compare::compare_expected_values,
    expect::get_expected_values,
    extract::{claims_set_from_serialized_cert, extract_event_data, extract_evidence},
    platform::verify_root_attestation_signature,
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
    policy: Box<dyn Policy>,
    clock: Box<dyn Clock>,
}

impl AmdSevSnpDiceAttestationVerifier {
    pub fn new(policy: Box<dyn Policy>, clock: Box<dyn Clock>) -> Self {
        Self { policy, clock }
    }
}

impl AttestationVerifier for AmdSevSnpDiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        // Last layer's certificate authority key is not used to sign anything.
        let _ = verify_dice_chain(evidence).context("couldn't verify DICE chain")?;

        // Verify event log and event endorsements with corresponding policy.
        let event_log = &evidence
            .event_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("event log was not provided"))?;
        let event_endorsements = &endorsements
            .event_endorsements
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("event endorsements were not provided"))?;
        self.policy.verify(event_log, event_endorsements, self.clock.get_milliseconds_since_epoch())
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
