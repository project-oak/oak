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

use alloc::{boxed::Box, sync::Arc, vec, vec::Vec};

use anyhow::Context;
use itertools::izip;
use oak_attestation_verification_types::{
    policy::{EventPolicy, Policy},
    verifier::AttestationVerifier,
};
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{
        AttestationResults, Endorsements, EventAttestationResults, EventLog, Evidence,
        ReferenceValues, attestation_results::Status, reference_values,
    },
};
use oak_tdx_quote::TdxQuoteWrapper;
use oak_time::{Clock, Instant};
use sha2::{Digest, Sha384};

use crate::{
    IntelTdxPolicy,
    intel::RtmrEmulator,
    policy::{
        application::ApplicationPolicy,
        container::ContainerPolicy,
        firmware::FirmwarePolicy,
        kernel::KernelPolicy,
        platform::{AmdSevSnpPolicy, InsecurePolicy},
        system::SystemPolicy,
    },
    results::get_initial_measurement,
    verifier::{EventLogType, verify_dice_chain},
};

// Base AMD SEV-SNP verifier that validates AMD SEV-SNP platform authenticity
// and configuration and the firmware measurement.
// TODO: b/452736849 - Utilize the `BaseAmdSevSnpVerifier` for the transparent
// attestation verifier.
struct BaseAmdSevSnpVerifier {
    platform_policy: AmdSevSnpPolicy,
    firmware_policy: Box<dyn EventPolicy>,
}

impl BaseAmdSevSnpVerifier {
    fn verify_platform(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
        verification_time: Instant,
    ) -> anyhow::Result<EventAttestationResults> {
        // Verify AMD SEV-SNP platform authenticity and configuration.
        let root_layer = evidence.root_layer.as_ref().context("no root layer in evidence")?;
        let platform_endorsement =
            endorsements.platform.as_ref().context("no platform endorsement")?;
        let platform_results = self
            .platform_policy
            .verify(verification_time, root_layer, platform_endorsement)
            .context("verifying platform policy")?;
        Ok(platform_results)
    }

    fn verify_firmware(
        &self,
        endorsements: &Endorsements,
        platform_results: &EventAttestationResults,
        verification_time: Instant,
    ) -> anyhow::Result<EventAttestationResults> {
        // Verify firmware measurement.
        let firmware_endorsement =
            &endorsements.initial.as_ref().context("no firmware endorsement")?;
        let measurement = get_initial_measurement(platform_results)
            .ok_or(anyhow::anyhow!("no initial measurement"))?;
        let firmware_results = self
            .firmware_policy
            .verify(verification_time, measurement, firmware_endorsement)
            .context("verifying firmware policy")?;
        Ok(firmware_results)
    }
}

/// Attestation verifier that verifies an attestation rooted in AMD SEV-SNP.
pub struct AmdSevSnpDiceAttestationVerifier {
    base_verifier: BaseAmdSevSnpVerifier,
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
        let base_verifier = BaseAmdSevSnpVerifier { platform_policy, firmware_policy };
        Self { base_verifier, event_policies, clock }
    }
}

/// Verifies an attestation rooted in AMD SEV-SNP. Verification fails if any
/// of the event verifiers fails.
impl AttestationVerifier for AmdSevSnpDiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        let platform_results = self
            .base_verifier
            .verify_platform(evidence, endorsements, verification_time)
            .context("verifying platform policy")?;

        // Verify DICE chain integrity.
        // The output argument is ommited because last layer's certificate authority key
        // is not used to sign anything.
        let _ = verify_dice_chain(evidence, EventLogType::OriginalEventLog)
            .context("verifying DICE chain")?;

        let firmware_results = self
            .base_verifier
            .verify_firmware(endorsements, &platform_results, verification_time)
            .context("verifying firmware policy")?;

        // Verify event log and event endorsements with corresponding policies.
        let event_log =
            evidence.event_log.as_ref().ok_or_else(|| anyhow::anyhow!("no event log"))?;
        let mut event_attestation_results = Vec::new();
        event_attestation_results.push(platform_results);
        event_attestation_results.push(firmware_results);
        if !endorsements.events.is_empty() {
            let results = verify_event_log(
                verification_time,
                event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("verifying event log")?;

            event_attestation_results.extend(results);
        }

        // TODO: b/366419879 - Combine per-event attestation results.
        Ok(AttestationResults {
            status: Status::Success.into(),
            extracted_evidence: None,
            event_attestation_results,
            ..Default::default()
        })
    }
}

/// Attestation verifier that verifies a transparent attestation (i.e. an
/// attestation with a transparent event log) rooted in AMD SEV-SNP.
pub struct AmdSevSnpTransparentDiceAttestationVerifier {
    base_verifier: BaseAmdSevSnpVerifier,
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Arc<dyn Clock>,
}

impl AmdSevSnpTransparentDiceAttestationVerifier {
    pub fn new(
        platform_policy: AmdSevSnpPolicy,
        firmware_policy: Box<dyn EventPolicy>,
        event_policies: Vec<Box<dyn EventPolicy>>,
        clock: Arc<dyn Clock>,
    ) -> Self {
        let base_verifier = BaseAmdSevSnpVerifier { platform_policy, firmware_policy };
        Self { base_verifier, event_policies, clock }
    }
}

impl AttestationVerifier for AmdSevSnpTransparentDiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        let platform_results = self
            .base_verifier
            .verify_platform(evidence, endorsements, verification_time)
            .context("verifying platform policy")?;

        // Verify DICE chain integrity.
        // The output argument is ommited because last layer's certificate authority key
        // is not used to sign anything.
        let _ = verify_dice_chain(evidence, EventLogType::TransparentEventLog)
            .context("verifying DICE chain")?;

        let firmware_results = self
            .base_verifier
            .verify_firmware(endorsements, &platform_results, verification_time)
            .context("verifying firmware policy")?;

        // Verify event log and event endorsements with corresponding policies.
        let transparent_event_log = evidence
            .transparent_event_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no event log"))?;
        let mut event_attestation_results = vec![platform_results, firmware_results];
        if !endorsements.events.is_empty() {
            let results = verify_event_log(
                verification_time,
                transparent_event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("verifying event log")?;

            event_attestation_results.extend(results);
        }

        Ok(AttestationResults {
            status: Status::Success.into(),
            extracted_evidence: None,
            event_attestation_results,
            ..Default::default()
        })
    }
}

/// Attestation verifier that verifies an attestation rooted in Intel TDX.
pub struct IntelTdxAttestationVerifier {
    platform_policy: IntelTdxPolicy,
    firmware_policy: Box<dyn EventPolicy>,
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Arc<dyn Clock>,
}

impl IntelTdxAttestationVerifier {
    pub fn new(
        platform_policy: IntelTdxPolicy,
        firmware_policy: Box<dyn EventPolicy>,
        event_policies: Vec<Box<dyn EventPolicy>>,
        clock: Arc<dyn Clock>,
    ) -> Self {
        Self { platform_policy, firmware_policy, event_policies, clock }
    }
}

/// Verifies an attestation rooted in Intel TDX. Verification fails if any
/// of the event verifiers fails.
impl AttestationVerifier for IntelTdxAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        // Verify Intel TDX platform authenticity and configuration.
        let root_layer = evidence.root_layer.as_ref().context("no root layer in evidence")?;
        let platform_endorsement =
            endorsements.platform.as_ref().context("no platform endorsement")?;
        let platform_results = self
            .platform_policy
            .verify(verification_time, root_layer, platform_endorsement)
            .context("verifying platform policy")?;

        // Verify firmware measurement.
        let firmware_endorsement =
            &endorsements.initial.as_ref().context("no firmware endorsement")?;
        let measurement = get_initial_measurement(&platform_results)
            .ok_or(anyhow::anyhow!("no initial measurement"))?;
        let firmware_results = self
            .firmware_policy
            .verify(verification_time, measurement, firmware_endorsement)
            .context("verifying firmware policy")?;

        let wrapper = TdxQuoteWrapper::new(root_layer.remote_attestation_report.as_slice());
        let expected = wrapper.parse_quote().expect("invalid quote").body.rtmr_2;

        let event_log =
            evidence.event_log.as_ref().ok_or_else(|| anyhow::anyhow!("no event log"))?;

        // Verify integrity of the event log.
        let mut rtmr_2 = RtmrEmulator::new();
        for entry in event_log.encoded_events.as_slice().iter() {
            rtmr_2.extend(&Sha384::digest(entry.as_slice()).into());
        }
        anyhow::ensure!(rtmr_2.get_state() == expected, "event log integrity check failed");

        // Verify event log and event endorsements with corresponding policies.
        let mut event_attestation_results = Vec::new();
        event_attestation_results.push(platform_results);
        event_attestation_results.push(firmware_results);
        if !endorsements.events.is_empty() {
            let results = verify_event_log(
                verification_time,
                event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("verifying event log")?;

            event_attestation_results.extend(results);
        }

        // TODO: b/366419879 - Combine per-event attestation results.
        Ok(AttestationResults {
            status: Status::Success.into(),
            extracted_evidence: None,
            event_attestation_results,
            ..Default::default()
        })
    }
}

/// Attestation verifier for cases when there is no hardware root of trust.
/// The attestation report contains just the root key, no stage0 measurement.
/// The endorsements of the events can still be verified against reference
/// values.
pub struct InsecureAttestationVerifier {
    clock: Arc<dyn Clock>,
    insecure_policy: InsecurePolicy,
    event_policies: Vec<Box<dyn EventPolicy>>,
}

impl InsecureAttestationVerifier {
    pub fn new(clock: Arc<dyn Clock>, event_policies: Vec<Box<dyn EventPolicy>>) -> Self {
        Self { clock, insecure_policy: InsecurePolicy::new(), event_policies }
    }
}

/// Verifies the validity of an empty and hence meaningless attestation
/// report, then verifies the DICE chain. Finally verifies the event log.
impl AttestationVerifier for InsecureAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        let root_layer = evidence.root_layer.as_ref().context("no root layer in evidence")?;
        let insecure_endorsement =
            endorsements.platform.as_ref().context("no platform endorsement")?;
        let insecure_results =
            self.insecure_policy.verify(verification_time, root_layer, insecure_endorsement)?;

        // Verify DICE chain integrity. The output argument is omitted because
        // the last layer's certificate authority key is not used to sign
        // anything.
        let _ = verify_dice_chain(evidence, EventLogType::OriginalEventLog)
            .context("verifying DICE chain")?;

        // Verify event log and event endorsements with corresponding policies.
        let event_log =
            evidence.event_log.as_ref().ok_or_else(|| anyhow::anyhow!("no event log"))?;
        let mut event_attestation_results = Vec::new();
        event_attestation_results.push(insecure_results);
        if !endorsements.events.is_empty() {
            let results = verify_event_log(
                verification_time,
                event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("verifying event log")?;

            event_attestation_results.extend(results);
        }

        Ok(AttestationResults {
            status: Status::Success.into(),
            extracted_evidence: None,
            event_attestation_results,
            ..Default::default()
        })
    }
}

// Attestation verifier that only verifies the EventLog, i.e. it doesn't verify
// the root attestation and doesn't check the DICE certificate chain.
pub struct EventLogVerifier {
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Arc<dyn Clock>,
}

impl EventLogVerifier {
    pub fn new(event_policies: Vec<Box<dyn EventPolicy>>, clock: Arc<dyn Clock>) -> Self {
        Self { event_policies, clock }
    }
}

// Verifies the EventLog in the evidence. Verification fails if any of
// the event verifiers fails.
impl AttestationVerifier for EventLogVerifier {
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
        .context("verifying event log")?;

        // TODO: b/366419879 - Combine per-event attestation results.
        Ok(AttestationResults {
            status: Status::Success.into(),
            extracted_evidence: None,
            event_attestation_results,
            ..Default::default()
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
            let amd = root_rvs.amd_sev.as_ref().context("no AMD SEV-SNP reference values")?;
            let platform_policy = AmdSevSnpPolicy::new(amd);
            let firmware_policy =
                FirmwarePolicy::new(amd.stage0.as_ref().context("no stage0 reference value")?);
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let system_policy = SystemPolicy::new(
                rvs.system_layer.as_ref().context("no system layer reference values")?,
            );
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
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let amd = root_rvs.amd_sev.as_ref().context("no AMD SEV-SNP reference values")?;
            let platform_policy = AmdSevSnpPolicy::new(amd);
            let firmware_policy =
                FirmwarePolicy::new(amd.stage0.as_ref().context("no firmware reference value")?);
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

// Creates an Intel TDX verifier from reference values.
pub fn create_intel_tdx_verifier<T: Clock + 'static>(
    clock: T,
    reference_values: &ReferenceValues,
) -> anyhow::Result<IntelTdxAttestationVerifier> {
    match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(rvs)) => {
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let intel_rvs = root_rvs.intel_tdx.as_ref().context("no Intel TDX reference values")?;
            let platform_policy = IntelTdxPolicy::new(intel_rvs);
            let firmware_policy = FirmwarePolicy::new(
                intel_rvs.stage0.as_ref().context("no stage0 reference value")?,
            );
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let system_policy = SystemPolicy::new(
                rvs.system_layer.as_ref().context("no system layer reference values")?,
            );
            let container_policy = ContainerPolicy::new(
                rvs.container_layer.as_ref().context("no container layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(system_policy), Box::new(container_policy)];

            Ok(IntelTdxAttestationVerifier::new(
                platform_policy,
                Box::new(firmware_policy),
                event_policies,
                Arc::new(clock),
            ))
        }
        Some(reference_values::Type::OakRestrictedKernel(_)) => {
            anyhow::bail!("Restricted Kernel verification on Intel TDX is not yet supported")
        }
        _ => anyhow::bail!("unsupported reference values"),
    }
}

// Creates a verifier for an attestation from hardware which is neither AMD
// SEV-SNP nor Intel TDX.
pub fn create_insecure_verifier<T: Clock + 'static>(
    clock: T,
    reference_values: &ReferenceValues,
) -> anyhow::Result<InsecureAttestationVerifier> {
    match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(rvs)) => {
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            anyhow::ensure!(root_rvs.insecure.is_some(), "insecure not allowed");
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let system_policy = SystemPolicy::new(
                rvs.system_layer.as_ref().context("no system layer reference values")?,
            );
            let container_policy = ContainerPolicy::new(
                rvs.container_layer.as_ref().context("no container layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(system_policy), Box::new(container_policy)];

            Ok(InsecureAttestationVerifier::new(Arc::new(clock), event_policies))
        }
        Some(reference_values::Type::OakRestrictedKernel(rvs)) => {
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            anyhow::ensure!(root_rvs.insecure.is_some(), "insecure not allowed");
            let kernel_policy = KernelPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let application_policy = ApplicationPolicy::new(
                rvs.application_layer.as_ref().context("no application layer reference values")?,
            );
            let event_policies: Vec<Box<dyn Policy<[u8]>>> =
                vec![Box::new(kernel_policy), Box::new(application_policy)];

            Ok(InsecureAttestationVerifier::new(Arc::new(clock), event_policies))
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
