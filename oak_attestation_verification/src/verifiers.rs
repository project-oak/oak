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
//

//! Provides verifiers based on verification policies.

use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
    vec,
    vec::Vec,
};

use anyhow::Context;
use hashbrown::HashSet;
use itertools::izip;
use oak_attestation_verification_types::{
    policy::{EventPolicy, Policy},
    verifier::AttestationVerifier,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, reference_values, AttestationResults, Endorsements,
        EventAttestationResults, EventLog, Evidence, ReferenceValues,
    },
    Variant,
};
use oak_sev_snp_attestation_report::AttestationReport;
use oak_time::{Clock, Instant};
use zerocopy::FromBytes;

use crate::{
    policy::{
        application::ApplicationPolicy, container::ContainerPolicy, firmware::FirmwarePolicy,
        kernel::KernelPolicy, platform::AmdSevSnpPolicy, system::SystemPolicy,
    },
    util::hash_sha2_256,
    verifier::verify_dice_chain,
};

pub struct AmdSevSnpDiceAttestationVerifier {
    platform_policy: AmdSevSnpPolicy,
    firmware_policy: Box<dyn EventPolicy>,
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Arc<dyn Clock>,
}

impl AmdSevSnpDiceAttestationVerifier {
    pub fn new(
        platform_policy: AmdSevSnpPolicy,
        firmware_policy: Box<dyn EventPolicy>,
        event_policies: Vec<Box<dyn EventPolicy>>,
        clock: Arc<dyn Clock>,
    ) -> Self {
        Self { platform_policy, firmware_policy, event_policies, clock }
    }
}

impl AttestationVerifier for AmdSevSnpDiceAttestationVerifier {
    // Verifies the AMD SEV-SNP attestation report and the EventLog in the
    // evidence and returns [`AttestationResults`] with the Success status if
    // verification is successful. Verification fails if one of the event
    // verifiers fails. In this case [`Result::Err`] is returned.
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        // Get DICE root layer evidence.
        let root_layer = &evidence
            .root_layer
            .as_ref()
            .context("root DICE layer wasn't provided in the evidence")?;

        // Parse AMD SEV-SNP attestation report.
        let attestation_report = AttestationReport::ref_from_bytes(
            &root_layer.remote_attestation_report,
        )
        .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))?;

        // Verify AMD SEV-SNP platform authenticity and configuration.
        let platform_endorsement = endorsements
            .platform
            .as_ref()
            .context("AMD SEV-SNP endorsement wasn't provided in endorsements")?;
        self.platform_policy
            .verify(verification_time, attestation_report, platform_endorsement)
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
        let firmware_attestation_result = self
            .firmware_policy
            .verify(verification_time, &attestation_report.data.measurement, firmware_endorsement)
            .context("couldn't verify firmware")?;

        // Verify event log and event endorsements with corresponding policies.
        let event_log = &evidence
            .event_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("event log was not provided"))?;
        let mut event_attestation_results = Vec::new();
        event_attestation_results.push(firmware_attestation_result);
        if !endorsements.events.is_empty() {
            let results = verify_event_log(
                verification_time,
                event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("couldn't verify event log")?;

            verify_event_artifacts_uniqueness(&results)
                .context("couldn't verify event artifacts uniqueness")?;
            event_attestation_results.extend(results);
        }

        // TODO: b/366419879 - Combine per-event attestation results.
        #[allow(deprecated)]
        Ok(AttestationResults {
            status: Status::Success.into(),
            reason: "".to_string(),
            encryption_public_key: vec![],
            signing_public_key: vec![],
            extracted_evidence: None,
            event_attestation_results,
        })
    }
}

// Attestation verifier that only verifies the EventLog, i.e. it doesn't verify
// the root attestation and doesn't check the DICE certificate chain.
// NB: this verifier returns attestation failures as Rust errors instead of the
// AttestationResults.
pub struct EventLogVerifier {
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Arc<dyn Clock>,
}

impl EventLogVerifier {
    pub fn new(event_policies: Vec<Box<dyn EventPolicy>>, clock: Arc<dyn Clock>) -> Self {
        Self { event_policies, clock }
    }
}

impl AttestationVerifier for EventLogVerifier {
    // Verifies the EventLog in the evidence and returns AttestationResults with the
    // Success status if verification is successful. Verification fails if one of
    // the event verifiers fails. In this case Result::Err is returned.
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        // Verify event log and event endorsements with corresponding policies.
        let event_log = &evidence
            .event_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("event log was not provided"))?;
        let event_endorsements = &endorsements.events;
        let event_attestation_results = verify_event_log(
            verification_time,
            event_log,
            event_endorsements,
            self.event_policies.as_slice(),
        )
        .context("couldn't verify event log")?;

        verify_event_artifacts_uniqueness(&event_attestation_results)
            .context("couldn't verify event artifacts ID uniqueness")?;

        // TODO: b/366419879 - Combine per-event attestation results.
        #[allow(deprecated)]
        Ok(AttestationResults {
            status: Status::Success.into(),
            reason: "".to_string(),
            encryption_public_key: vec![],
            signing_public_key: vec![],
            extracted_evidence: None,
            event_attestation_results,
        })
    }
}

// Creates an AMD SEV-SNP verifier from reference values.
pub fn create_amd_verifier<T: Clock + 'static>(
    clock: T,
    reference_values: &ReferenceValues,
) -> anyhow::Result<AmdSevSnpDiceAttestationVerifier> {
    match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(rvs)) => {
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let platform_policy = AmdSevSnpPolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create platform policy")?;
            let firmware_policy = FirmwarePolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create firmware policy")?;
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let system_policy = SystemPolicy::new(
                rvs.system_layer.as_ref().context("no system layer reference values")?,
            );
            // TODO: b/382550581 - Container reference values currently skip verification.
            let container_policy = ContainerPolicy::new(
                rvs.container_layer.as_ref().context("no container layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(system_policy), Box::new(container_policy)];

            Ok(AmdSevSnpDiceAttestationVerifier::new(
                platform_policy,
                Box::new(firmware_policy),
                event_policies,
                Arc::new(clock),
            ))
        }
        Some(reference_values::Type::OakRestrictedKernel(rvs)) => {
            // Create platform and firmware policies.
            // TODO: b/398859203 - Remove root layer reference values once old reference
            // values have been updated.
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let platform_policy = AmdSevSnpPolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create platform policy")?;
            let firmware_policy = FirmwarePolicy::from_root_layer_reference_values(root_rvs)
                .context("failed to create firmware policy")?;
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            // TODO: b/382550581 - Application reference values currently skip verification.
            let application_policy = ApplicationPolicy::new(
                rvs.application_layer.as_ref().context("no application layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(application_policy)];

            Ok(AmdSevSnpDiceAttestationVerifier::new(
                platform_policy,
                Box::new(firmware_policy),
                event_policies,
                Arc::new(clock),
            ))
        }
        _ => anyhow::bail!("malformed reference values"),
    }
}

/// Verifies an event log using a combination of event policies.
///
/// Event policies are provided as a list where each element corresponds to an
/// [`Event`] in the [`EventLog`] and [`EventEndorsement`] in the
/// [`EventEndorsements`] with the same index. This means that mapping between
/// policies and events is done via ordering.
fn verify_event_log(
    verification_time: Instant,
    event_log: &EventLog,
    event_endorsements: &[Variant],
    policies: &[Box<dyn EventPolicy>],
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
        padded_event_endorsements.extend(core::iter::repeat_n(
            &empty_endorsement,
            event_log.encoded_events.len() - event_endorsements.len(),
        ));
    }

    let verification_iterator =
        izip!(policies.iter(), event_log.encoded_events.iter(), padded_event_endorsements.iter());
    verification_iterator
        .map(|(event_policy, event, event_endorsement)| {
            event_policy.verify(verification_time, event, event_endorsement)
        })
        .collect::<Result<Vec<EventAttestationResults>, anyhow::Error>>()
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

#[cfg(test)]
mod tests;
