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
use oak_digest::Sha384;
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{
        AttestationResults, Endorsements, Event, EventAttestationResults, EventLog, Evidence,
        ReferenceValues, attestation_results::Status, reference_values,
    },
};
use oak_tdx_quote::TdxQuoteWrapper;
use oak_time::{Clock, Instant};
use prost::Message;

use crate::{
    IntelTdxPolicy,
    intel::RtmrEmulator,
    policy::{
        application::ApplicationPolicy,
        cb_transparent::{
            TdxRootTransparentPolicy, TransparentLayer1Policy, TransparentLayer2Policy,
        },
        container::ContainerPolicy,
        firmware::FirmwarePolicy,
        kernel::KernelPolicy,
        platform::{AmdSevSnpPolicy, InsecurePolicy},
        system::SystemPolicy,
    },
    results::get_initial_measurement,
    util::decode_protobuf_any,
    verifier::{EventLogType, verify_dice_chain, verify_user_data_certificate},
};

const NON_LAYER_TRANSPARENT_EVENT_TAGS: [&str; 2] = ["CCEL", "CCELTable"];
const BYTES_VALUE_TYPE_URL: &str = "type.googleapis.com/google.protobuf.BytesValue";

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

pub struct RestrictedKernelVerificationReport {
    pub session_binding_public_key: Vec<u8>,
}

impl RestrictedKernelVerificationReport {
    pub fn into_session_binding_public_key(self) -> anyhow::Result<Vec<u8>> {
        Ok(self.session_binding_public_key)
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

    pub fn report(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<RestrictedKernelVerificationReport> {
        let _results = self.verify(evidence, endorsements)?;
        let extracted_evidence = crate::extract_evidence(evidence)?;
        Ok(RestrictedKernelVerificationReport {
            session_binding_public_key: extracted_evidence.signing_public_key,
        })
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
        if !self.event_policies.is_empty() {
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
        // The output argument is recorded because it can be used to verify the
        // `Evidence.signed_user_data_certificate` structure.
        let last_layer_verifying_key =
            verify_dice_chain(evidence, EventLogType::TransparentEventLog)
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
        if !self.event_policies.is_empty() {
            let results = verify_event_log(
                verification_time,
                transparent_event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("verifying event log")?;

            event_attestation_results.extend(results);
        }

        // Attestation has been verified. We now verify the signed user data
        // certificate, if present.
        if !evidence.signed_user_data_certificate.is_empty() {
            let user_data_result = verify_user_data_certificate(
                &evidence.signed_user_data_certificate,
                &last_layer_verifying_key,
            )
            .context("verifying signed user data certificate")?;
            event_attestation_results.push(user_data_result);
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
        //
        // The platform policy is also responsible for extracting the initial
        // measurement, which implicitly includes the firmware. This is stored as an
        // artifact in the platform results and later retrieved to verify it with the
        // firmware policy.
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
            rtmr_2.extend(&Sha384::from_contents(entry.as_slice()).into());
        }
        anyhow::ensure!(rtmr_2.get_state() == expected, "event log integrity check failed");

        // Verify event log and event endorsements with corresponding policies.
        let mut event_attestation_results = Vec::new();
        event_attestation_results.push(platform_results);
        event_attestation_results.push(firmware_results);
        if !self.event_policies.is_empty() {
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

fn filter_non_layer_transparent_events(evidence: &Evidence) -> anyhow::Result<Evidence> {
    let transparent_event_log =
        evidence.transparent_event_log.as_ref().context("no transparent event log")?;
    let mut seen = [false; NON_LAYER_TRANSPARENT_EVENT_TAGS.len()];
    let mut encoded_events = Vec::with_capacity(transparent_event_log.encoded_events.len());

    for encoded_event in &transparent_event_log.encoded_events {
        if let Ok(event) = Event::decode(encoded_event.as_slice())
            && let Some(tag_idx) =
                NON_LAYER_TRANSPARENT_EVENT_TAGS.iter().position(|tag| *tag == event.tag)
            && event.event.as_ref().is_some_and(|any| {
                decode_protobuf_any::<Vec<u8>>(BYTES_VALUE_TYPE_URL, any).is_ok()
            })
        {
            anyhow::ensure!(!seen[tag_idx], "duplicate non-layer transparent event: {}", event.tag);
            seen[tag_idx] = true;
            continue;
        }
        encoded_events.push(encoded_event.clone());
    }

    Ok(Evidence {
        root_layer: evidence.root_layer.clone(),
        layers: evidence.layers.clone(),
        application_keys: evidence.application_keys.clone(),
        transparent_event_log: Some(EventLog { encoded_events }),
        ..Default::default()
    })
}

/// Attestation verifier for transparent attestations rooted in Intel TDX.
///
/// Strips at most one `"CCEL"` and one `"CCELTable"` non-layer event from
/// `transparent_event_log` before DICE verification (without RTMR replay yet).
/// Requires a non-empty `root_layer.eca_public_key` and `endorsements.initial`,
/// while tolerating `endorsements.platform == None`.
pub struct IntelTdxTransparentDiceAttestationVerifier {
    platform_policy: IntelTdxPolicy,
    firmware_policy: Box<dyn EventPolicy>,
    event_policies: Vec<Box<dyn EventPolicy>>,
    clock: Arc<dyn Clock>,
}

impl IntelTdxTransparentDiceAttestationVerifier {
    pub fn new(
        platform_policy: IntelTdxPolicy,
        firmware_policy: Box<dyn EventPolicy>,
        event_policies: Vec<Box<dyn EventPolicy>>,
        clock: Arc<dyn Clock>,
    ) -> Self {
        Self { platform_policy, firmware_policy, event_policies, clock }
    }

    fn verify_after_platform(
        &self,
        verification_time: Instant,
        platform_results: EventAttestationResults,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let filtered_evidence = filter_non_layer_transparent_events(evidence)?;

        // Verify DICE chain integrity against the filtered transparent event log.
        let last_layer_verifying_key =
            verify_dice_chain(&filtered_evidence, EventLogType::TransparentEventLog)
                .context("verifying DICE chain")?;

        let firmware_endorsement =
            endorsements.initial.as_ref().context("no firmware endorsement")?;
        let measurement = get_initial_measurement(&platform_results)
            .ok_or_else(|| anyhow::anyhow!("no initial measurement"))?;
        let firmware_results = self
            .firmware_policy
            .verify(verification_time, measurement, firmware_endorsement)
            .context("verifying firmware policy")?;

        let transparent_event_log =
            filtered_evidence.transparent_event_log.as_ref().context("no transparent event log")?;
        let mut event_attestation_results = vec![platform_results, firmware_results];
        if !self.event_policies.is_empty() {
            let results = verify_event_log(
                verification_time,
                transparent_event_log,
                &endorsements.events,
                self.event_policies.as_slice(),
            )
            .context("verifying event log")?;
            event_attestation_results.extend(results);
        }

        if !evidence.signed_user_data_certificate.is_empty() {
            let user_data_result = verify_user_data_certificate(
                &evidence.signed_user_data_certificate,
                &last_layer_verifying_key,
            )
            .context("verifying signed user data certificate")?;
            event_attestation_results.push(user_data_result);
        }

        Ok(AttestationResults {
            status: Status::Success.into(),
            extracted_evidence: None,
            event_attestation_results,
            ..Default::default()
        })
    }
}

impl AttestationVerifier for IntelTdxTransparentDiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();
        let root_layer = evidence.root_layer.as_ref().context("no root layer in evidence")?;
        anyhow::ensure!(!root_layer.eca_public_key.is_empty(), "empty root ECA public key");

        let default_endorsement = Variant::default();
        let platform_endorsement = endorsements.platform.as_ref().unwrap_or(&default_endorsement);
        let platform_results = self
            .platform_policy
            .verify(verification_time, root_layer, platform_endorsement)
            .context("verifying platform policy")?;

        self.verify_after_platform(verification_time, platform_results, evidence, endorsements)
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
        if !self.event_policies.is_empty() {
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

/// Creates an Intel TDX transparent DICE verifier from
/// `CbTransparentReferenceValues`, wiring [`TransparentLayer2Policy`] via
/// [`Policy::verify`].
pub fn create_intel_tdx_transparent_dice_verifier<T: Clock + 'static>(
    clock: T,
    reference_values: &ReferenceValues,
) -> anyhow::Result<IntelTdxTransparentDiceAttestationVerifier> {
    match reference_values.r#type.as_ref() {
        Some(reference_values::Type::Cbt(rvs)) => {
            let root_rvs = rvs.root_layer.as_ref().context("no root layer reference values")?;
            let intel_rvs = root_rvs.intel_tdx.as_ref().context("no Intel TDX reference values")?;
            let platform_policy = IntelTdxPolicy::new(intel_rvs);
            let firmware_policy = FirmwarePolicy::new(
                intel_rvs.stage0.as_ref().context("no stage0 reference value")?,
            );
            let layer0_policy = TdxRootTransparentPolicy::new(
                rvs.kernel_layer.as_ref().context("no kernel layer reference values")?,
            );
            let layer1_policy = TransparentLayer1Policy::new(
                rvs.layer1.as_ref().context("no layer1 reference values")?,
            );
            let layer2_policy = TransparentLayer2Policy::new(
                rvs.layer2.as_ref().context("no layer2 reference values")?,
            );
            let event_policies: Vec<Box<dyn EventPolicy>> =
                vec![Box::new(layer0_policy), Box::new(layer1_policy), Box::new(layer2_policy)];

            Ok(IntelTdxTransparentDiceAttestationVerifier::new(
                platform_policy,
                Box::new(firmware_policy),
                event_policies,
                Arc::new(clock),
            ))
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

#[cfg(test)]
mod tests {
    use alloc::{string::ToString, vec};

    use coset::{
        CborSerializable, CoseSign1Builder, HeaderBuilder, cbor::value::Value, cwt::ClaimName, iana,
    };
    use ecdsa::signature::Signer;
    use oak_dice::cert::{
        APPLICATION_KEYS_ADDITIONAL_DATA, DICE_LAYER_ADDITIONAL_DATA, SHA2_256_ID,
        TRANSPARENT_EVENT_ID, USER_DATA_ADDITIONAL_DATA, derive_verifying_key_id,
        generate_ecdsa_key_pair, generate_kem_certificate_with_aad,
        generate_signing_certificate_with_aad, verifying_key_to_cose_key,
    };
    use oak_digest::Sha256;
    use oak_proto_rust::oak::{
        RawDigest,
        attestation::v1::{
            ApplicationKeys, BinaryReferenceValue, CbLayer1TransparentEndorsement,
            CbLayer1TransparentEvent, CbLayer1TransparentReferenceValues,
            CbLayer2TransparentEndorsement, CbLayer2TransparentEvent,
            CbLayer2TransparentReferenceValues, CbTransparentReferenceValues, Digests,
            IntelTdxReferenceValues, KernelBinaryReferenceValue, KernelEndorsement,
            KernelLayerReferenceValues, LayerEvidence, MpmPackage, MpmReferenceValue,
            MpmVersionIds, RootLayerEvidence, RootLayerReferenceValues, SkipVerification,
            TdxTcbSvnReferenceValue, TeePlatform, TextReferenceValue, binary_reference_value,
            kernel_binary_reference_value, mpm_reference_value, tdx_tcb_svn_reference_value,
            text_reference_value,
        },
    };
    use oak_time::{clock::FixedClock, make_instant};
    use p256::ecdsa::{Signature, SigningKey, VerifyingKey};
    use prost_types::Any;
    use test_util::AttestationData;

    use super::*;
    use crate::results::{get_user_data_payload, set_initial_measurement};

    fn valid_time() -> Instant {
        make_instant!("2025-10-15T00:00:00Z")
    }

    fn encode_event(tag: &str, type_url: &str, value: Vec<u8>) -> Vec<u8> {
        Event { tag: tag.to_string(), event: Some(Any { type_url: type_url.to_string(), value }) }
            .encode_to_vec()
    }

    type CbtMutator = fn(&mut CbTransparentReferenceValues);

    fn assert_err_contains(err: anyhow::Error, expected: &str) {
        assert!(format!("{err:#}").contains(expected), "expected `{expected}` in error: {err:#}");
    }

    fn make_minimal_cbt() -> CbTransparentReferenceValues {
        let skip = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
        };
        CbTransparentReferenceValues {
            root_layer: Some(RootLayerReferenceValues {
                intel_tdx: Some(IntelTdxReferenceValues {
                    tee_tcb_svn: Some(TdxTcbSvnReferenceValue {
                        r#type: Some(tdx_tcb_svn_reference_value::Type::Skip(SkipVerification {})),
                    }),
                    allow_debug: false,
                    stage0: Some(skip),
                }),
                ..Default::default()
            }),
            kernel_layer: Some(KernelLayerReferenceValues::default()),
            layer1: Some(CbLayer1TransparentReferenceValues::default()),
            layer2: Some(CbLayer2TransparentReferenceValues::default()),
        }
    }

    #[test]
    fn filter_non_layer_transparent_events_handles_valid_and_invalid_logs() {
        assert_err_contains(
            filter_non_layer_transparent_events(&Evidence::default()).unwrap_err(),
            "no transparent event log",
        );
        let l0 =
            encode_event("tdxRootTransparent", "type.googleapis.com/google.protobuf.Empty", vec![]);
        let l1 = encode_event("layer1Transparent", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x01, 0x01]);
        let l2 = encode_event("layer2Transparent", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x01, 0x02]);
        let ccel = encode_event("CCEL", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x02, 0x01, 0x02]);
        let ccel_t = encode_event("CCELTable", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x02, 0x03, 0x04]);
        let ev = |encoded_events| Evidence {
            transparent_event_log: Some(EventLog { encoded_events }),
            ..Default::default()
        };

        for log in [
            vec![l0.clone(), l1.clone(), ccel.clone(), ccel_t.clone(), l2.clone()],
            vec![ccel.clone(), ccel_t.clone(), l0.clone(), l1.clone(), l2.clone()],
        ] {
            let out = filter_non_layer_transparent_events(&ev(log)).unwrap();
            assert_eq!(
                out.transparent_event_log.unwrap().encoded_events,
                vec![l0.clone(), l1.clone(), l2.clone()]
            );
        }
        // Keep malformed or spoofed CCEL entries so DICE chain verification rejects
        // them.
        for bad in [
            Event { tag: "CCEL".to_string(), event: None }.encode_to_vec(),
            encode_event("CCEL", BYTES_VALUE_TYPE_URL, vec![0x08, 0x01]),
            encode_event("CCEL", "type.googleapis.com/other.Msg", vec![]),
        ] {
            let out =
                filter_non_layer_transparent_events(&ev(vec![l0.clone(), bad.clone()])).unwrap();
            assert_eq!(out.transparent_event_log.unwrap().encoded_events, vec![l0.clone(), bad]);
        }
        assert_err_contains(
            filter_non_layer_transparent_events(&ev(vec![ccel.clone(), ccel])).unwrap_err(),
            "duplicate non-layer transparent event: CCEL",
        );
        assert_err_contains(
            filter_non_layer_transparent_events(&ev(vec![ccel_t.clone(), ccel_t])).unwrap_err(),
            "duplicate non-layer transparent event: CCELTable",
        );
    }

    #[test]
    fn tdx_transparent_verify_real_quote_rejects_empty_mismatched_key_and_non_tdx() {
        let d = AttestationData::load_tdx_oc();
        let rvs = ReferenceValues { r#type: Some(reference_values::Type::Cbt(make_minimal_cbt())) };
        let verifier = create_intel_tdx_transparent_dice_verifier(
            FixedClock::at_instant(d.make_valid_time()),
            &rvs,
        )
        .expect("factory should succeed");
        let mut endorsements =
            Endorsements { initial: Some(Variant::default()), ..Default::default() };

        assert_err_contains(
            verifier.verify(&d.evidence, &endorsements).unwrap_err(),
            "empty root ECA public key",
        );
        let mut mismatched = d.evidence.clone();
        let (_, other_pub) = generate_ecdsa_key_pair();
        mismatched.root_layer.as_mut().unwrap().eca_public_key =
            verifying_key_to_cose_key(&other_pub).to_vec().unwrap();
        for platform_endorsement in [None, Some(Variant::default())] {
            endorsements.platform = platform_endorsement;
            assert_err_contains(
                verifier.verify(&mismatched, &endorsements).unwrap_err(),
                "not bound to the Intel TDX attestation quote",
            );
        }
        for platform in [TeePlatform::None, TeePlatform::AmdSevSnp, TeePlatform::Unspecified] {
            let mut non_tdx = mismatched.clone();
            non_tdx.root_layer.as_mut().unwrap().platform = platform.into();
            assert_err_contains(
                verifier.verify(&non_tdx, &endorsements).unwrap_err(),
                "unsupported TEE platform value",
            );
        }
    }

    #[test]
    fn create_intel_tdx_transparent_dice_verifier_rejects_invalid_reference_values() {
        let d_tdx_oc = AttestationData::load_tdx_oc();
        assert_err_contains(
            create_intel_tdx_transparent_dice_verifier(
                FixedClock::at_instant(valid_time()),
                &d_tdx_oc.reference_values,
            )
            .err()
            .unwrap(),
            "unsupported reference values",
        );
        let base_cbt = make_minimal_cbt();
        let cases: &[(&str, CbtMutator)] = &[
            ("no root layer reference values", |c| c.root_layer = None),
            ("no Intel TDX reference values", |c| c.root_layer.as_mut().unwrap().intel_tdx = None),
            ("no stage0 reference value", |c| {
                c.root_layer.as_mut().unwrap().intel_tdx.as_mut().unwrap().stage0 = None
            }),
            ("no kernel layer reference values", |c| c.kernel_layer = None),
            ("no layer1 reference values", |c| c.layer1 = None),
            ("no layer2 reference values", |c| c.layer2 = None),
        ];
        for (expected, mutate) in cases {
            let mut cbt = base_cbt.clone();
            mutate(&mut cbt);
            let rv = ReferenceValues { r#type: Some(reference_values::Type::Cbt(cbt)) };
            assert_err_contains(
                create_intel_tdx_transparent_dice_verifier(
                    FixedClock::at_instant(valid_time()),
                    &rv,
                )
                .err()
                .unwrap(),
                expected,
            );
        }
    }

    fn digest_brv(sha2_256: Vec<u8>, sha2_384: Vec<u8>) -> BinaryReferenceValue {
        BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![RawDigest { sha2_256, sha2_384, ..Default::default() }],
            })),
        }
    }

    fn build_transparent_dice_layer(
        issuer_key: &SigningKey,
        issuer_verifying_key: &VerifyingKey,
        subject_verifying_key: &VerifyingKey,
        encoded_event: &[u8],
    ) -> LayerEvidence {
        let issuer_id = hex::encode(derive_verifying_key_id(issuer_verifying_key));
        let digest = Sha256::from_contents(encoded_event);
        let claim = (
            ClaimName::PrivateUse(TRANSPARENT_EVENT_ID),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(digest.as_ref().to_vec()),
            )]),
        );
        let cert = generate_signing_certificate_with_aad(
            issuer_key,
            issuer_id,
            subject_verifying_key,
            vec![claim],
            DICE_LAYER_ADDITIONAL_DATA,
        )
        .expect("failed to generate layer cert")
        .to_vec()
        .expect("failed to serialize layer cert");
        LayerEvidence { eca_certificate: cert }
    }

    fn build_signed_user_data_cert(signing_key: &SigningKey, payload: &[u8]) -> Vec<u8> {
        let protected = HeaderBuilder::new().algorithm(iana::Algorithm::ES256).build();
        CoseSign1Builder::new()
            .protected(protected)
            .payload(payload.to_vec())
            .create_signature(USER_DATA_ADDITIONAL_DATA, |data| {
                let signature: Signature = signing_key.sign(data);
                signature.to_bytes().as_slice().into()
            })
            .build()
            .to_vec()
            .expect("failed to serialize user data cert")
    }

    fn build_application_keys(
        issuer_key: &SigningKey,
        issuer_verifying_key: &VerifyingKey,
    ) -> ApplicationKeys {
        let issuer_id = hex::encode(derive_verifying_key_id(issuer_verifying_key));
        let (_, app_verifying_key) = generate_ecdsa_key_pair();
        let signing_cert = generate_signing_certificate_with_aad(
            issuer_key,
            issuer_id.clone(),
            &app_verifying_key,
            vec![],
            APPLICATION_KEYS_ADDITIONAL_DATA,
        )
        .expect("failed to generate app signing cert")
        .to_vec()
        .expect("failed to serialize app signing cert");
        let encryption_cert = generate_kem_certificate_with_aad(
            issuer_key,
            issuer_id,
            &[0x33u8; 32],
            vec![],
            APPLICATION_KEYS_ADDITIONAL_DATA,
        )
        .expect("failed to generate app encryption cert")
        .to_vec()
        .expect("failed to serialize app encryption cert");
        ApplicationKeys {
            encryption_public_key_certificate: encryption_cert,
            signing_public_key_certificate: signing_cert,
            ..Default::default()
        }
    }

    struct TdxTransparentFixture {
        evidence: Evidence,
        endorsements: Endorsements,
        reference_values: ReferenceValues,
        platform_results: EventAttestationResults,
        layer0_event: Vec<u8>,
        layer1_event: Vec<u8>,
        layer2_event: Vec<u8>,
        ccel_event: Vec<u8>,
        ccel_table_event: Vec<u8>,
        final_layer_key: SigningKey,
    }

    fn build_tdx_transparent_fixture() -> TdxTransparentFixture {
        let (root_priv, root_pub) = generate_ecdsa_key_pair();
        let (l1_priv, l1_pub) = generate_ecdsa_key_pair();
        let (l2_priv, l2_pub) = generate_ecdsa_key_pair();
        let (final_priv, final_pub) = generate_ecdsa_key_pair();
        let runtime_digest = vec![0x11u8; 32];
        let userspace_digest = vec![0x22u8; 32];
        let mr_td = vec![0x42u8; 48];
        let mpm_version = "workload/1.0".to_string();

        let layer0_event =
            encode_event("tdxRootTransparent", "type.googleapis.com/google.protobuf.Empty", vec![]);
        let layer1_event = encode_event(
            "layer1Transparent",
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            CbLayer1TransparentEvent {
                runtime_agent_binary_measurement: runtime_digest.clone(),
                userspace_measurement: userspace_digest.clone(),
                ..Default::default()
            }
            .encode_to_vec(),
        );
        let layer2_event = encode_event(
            "layer2Transparent",
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            CbLayer2TransparentEvent {
                packages: vec![MpmPackage {
                    mpm_version_id: mpm_version.clone(),
                    ..Default::default()
                }],
            }
            .encode_to_vec(),
        );
        let ccel_event = encode_event("CCEL", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x02, 0x01, 0x02]);
        let ccel_table_event =
            encode_event("CCELTable", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x02, 0x03, 0x04]);

        let evidence = Evidence {
            root_layer: Some(RootLayerEvidence {
                platform: TeePlatform::IntelTdx.into(),
                remote_attestation_report: vec![],
                eca_public_key: verifying_key_to_cose_key(&root_pub).to_vec().unwrap(),
            }),
            layers: vec![
                build_transparent_dice_layer(&root_priv, &root_pub, &l1_pub, &layer0_event),
                build_transparent_dice_layer(&l1_priv, &l1_pub, &l2_pub, &layer1_event),
                build_transparent_dice_layer(&l2_priv, &l2_pub, &final_pub, &layer2_event),
            ],
            application_keys: Some(build_application_keys(&final_priv, &final_pub)),
            transparent_event_log: Some(EventLog {
                encoded_events: vec![
                    layer0_event.clone(),
                    layer1_event.clone(),
                    ccel_event.clone(),
                    ccel_table_event.clone(),
                    layer2_event.clone(),
                ],
            }),
            signed_user_data_certificate: build_signed_user_data_cert(
                &final_priv,
                b"tdx-user-data",
            ),
            ..Default::default()
        };
        let endorsements = Endorsements {
            platform: None,
            initial: Some(Variant::default()),
            events: vec![
                KernelEndorsement::default().into(),
                CbLayer1TransparentEndorsement::default().into(),
                CbLayer2TransparentEndorsement::default().into(),
            ],
            ..Default::default()
        };
        let skip = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
        };
        let mut cbt = make_minimal_cbt();
        cbt.root_layer.as_mut().unwrap().intel_tdx.as_mut().unwrap().stage0 =
            Some(digest_brv(vec![], mr_td.clone()));
        cbt.kernel_layer = Some(KernelLayerReferenceValues {
            kernel: Some(KernelBinaryReferenceValue {
                r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
            }),
            kernel_cmd_line_text: Some(TextReferenceValue {
                r#type: Some(text_reference_value::Type::Skip(SkipVerification {})),
            }),
            init_ram_fs: Some(skip.clone()),
            memory_map: Some(skip.clone()),
            acpi: Some(skip),
        });
        cbt.layer1 = Some(CbLayer1TransparentReferenceValues {
            runtime_agent_binary: Some(digest_brv(runtime_digest, vec![])),
            userspace: Some(digest_brv(userspace_digest, vec![])),
            ..Default::default()
        });
        cbt.layer2 = Some(CbLayer2TransparentReferenceValues {
            binary_mpms: vec![MpmReferenceValue {
                r#type: Some(mpm_reference_value::Type::Versions(MpmVersionIds {
                    versions: vec![mpm_version],
                })),
            }],
            ..Default::default()
        });
        let reference_values = ReferenceValues { r#type: Some(reference_values::Type::Cbt(cbt)) };
        let mut platform_results = EventAttestationResults::default();
        set_initial_measurement(&mut platform_results, &mr_td);

        TdxTransparentFixture {
            evidence,
            endorsements,
            reference_values,
            platform_results,
            layer0_event,
            layer1_event,
            layer2_event,
            ccel_event,
            ccel_table_event,
            final_layer_key: final_priv,
        }
    }

    fn make_verifier(rvs: &ReferenceValues) -> IntelTdxTransparentDiceAttestationVerifier {
        create_intel_tdx_transparent_dice_verifier(FixedClock::at_instant(valid_time()), rvs)
            .expect("factory should succeed")
    }

    fn verify_synthetic(
        verifier: &IntelTdxTransparentDiceAttestationVerifier,
        platform_results: &EventAttestationResults,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        verifier.verify_after_platform(
            valid_time(),
            platform_results.clone(),
            evidence,
            endorsements,
        )
    }

    #[test]
    fn tdx_transparent_verify_after_platform_ccel_interleaved_and_leading_succeeds() {
        let mut fixture = build_tdx_transparent_fixture();
        let verifier = make_verifier(&fixture.reference_values);

        // Interleaved: [tdxRootTransparent, layer1, CCEL, CCELTable, layer2]
        let results = verify_synthetic(
            &verifier,
            &fixture.platform_results,
            &fixture.evidence,
            &fixture.endorsements,
        )
        .expect("interleaved CCEL transparent verification should succeed");
        assert_eq!(results.status, Status::Success as i32);
        assert_eq!(
            results.event_attestation_results.len(),
            6,
            "expected [platform, firmware, layer0, layer1, layer2, user_data]"
        );
        assert_eq!(
            get_user_data_payload(&results.event_attestation_results[5]).map(|v| v.as_slice()),
            Some(b"tdx-user-data".as_slice())
        );

        // Leading: [CCEL, CCELTable, tdxRootTransparent, layer1, layer2]
        fixture.evidence.transparent_event_log = Some(EventLog {
            encoded_events: vec![
                fixture.ccel_event.clone(),
                fixture.ccel_table_event.clone(),
                fixture.layer0_event.clone(),
                fixture.layer1_event.clone(),
                fixture.layer2_event.clone(),
            ],
        });
        let results_leading = verify_synthetic(
            &verifier,
            &fixture.platform_results,
            &fixture.evidence,
            &fixture.endorsements,
        )
        .expect("leading CCEL transparent verification should succeed");
        assert_eq!(results_leading.event_attestation_results.len(), 6);
    }

    #[test]
    fn tdx_transparent_verify_after_platform_without_user_data_or_app_keys_succeeds() {
        let mut fixture = build_tdx_transparent_fixture();
        fixture.evidence.signed_user_data_certificate.clear();
        let verifier = make_verifier(&fixture.reference_values);

        let results = verify_synthetic(
            &verifier,
            &fixture.platform_results,
            &fixture.evidence,
            &fixture.endorsements,
        )
        .expect("verification without user data cert should succeed");
        assert_eq!(results.event_attestation_results.len(), 5);

        fixture.evidence.application_keys = None;
        let results = verify_synthetic(
            &verifier,
            &fixture.platform_results,
            &fixture.evidence,
            &fixture.endorsements,
        )
        .expect("verification without application keys should succeed");
        assert_eq!(results.event_attestation_results.len(), 5);
    }

    fn expect_synthetic_err(
        verifier: &IntelTdxTransparentDiceAttestationVerifier,
        platform_results: &EventAttestationResults,
        evidence: &Evidence,
        endorsements: &Endorsements,
        expected: &str,
    ) {
        assert_err_contains(
            verify_synthetic(verifier, platform_results, evidence, endorsements).unwrap_err(),
            expected,
        );
    }

    #[test]
    fn tdx_transparent_verify_after_platform_swapped_dice_chain_fails() {
        let mut fixture = build_tdx_transparent_fixture();
        let verifier = make_verifier(&fixture.reference_values);

        // Regression for b/576709814: mismatched root_layer.eca_public_key fails DICE
        // chain verification.
        let (_, other_root_pub) = generate_ecdsa_key_pair();
        fixture.evidence.root_layer.as_mut().unwrap().eca_public_key =
            verifying_key_to_cose_key(&other_root_pub).to_vec().unwrap();
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &fixture.evidence,
            &fixture.endorsements,
            "verifying DICE chain",
        );
    }

    #[test]
    fn tdx_transparent_verify_after_platform_rejects_tampered_inner_layers_and_app_keys() {
        let fixture = build_tdx_transparent_fixture();
        let verifier = make_verifier(&fixture.reference_values);

        for layer_idx in [1usize, 2usize] {
            let mut bad_layer = fixture.evidence.clone();
            let cert = &mut bad_layer.layers[layer_idx].eca_certificate;
            let last = cert.len() - 1;
            cert[last] ^= 0x01;
            expect_synthetic_err(
                &verifier,
                &fixture.platform_results,
                &bad_layer,
                &fixture.endorsements,
                "verifying DICE chain",
            );
        }

        let (other_priv, other_pub) = generate_ecdsa_key_pair();
        let wrong_app_keys = build_application_keys(&other_priv, &other_pub);
        let mut bad_enc_key = fixture.evidence.clone();
        bad_enc_key.application_keys.as_mut().unwrap().encryption_public_key_certificate =
            wrong_app_keys.encryption_public_key_certificate;
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &bad_enc_key,
            &fixture.endorsements,
            "verifying application keys",
        );

        let mut bad_sig_key = fixture.evidence.clone();
        bad_sig_key.application_keys.as_mut().unwrap().signing_public_key_certificate =
            wrong_app_keys.signing_public_key_certificate;
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &bad_sig_key,
            &fixture.endorsements,
            "verifying application keys",
        );
    }

    #[test]
    fn tdx_transparent_verify_after_platform_rejects_unrecognized_spoofed_or_duplicate_events() {
        let fixture = build_tdx_transparent_fixture();
        let verifier = make_verifier(&fixture.reference_values);

        let pushed_cases = [
            (
                encode_event("KernelCmdline", BYTES_VALUE_TYPE_URL, vec![0x0a, 0x01, 0x01]),
                "verifying DICE chain",
            ),
            (vec![0xff, 0xff, 0xff], "verifying DICE chain"),
            (
                encode_event(
                    "CCEL",
                    "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
                    CbLayer1TransparentEvent::default().encode_to_vec(),
                ),
                "verifying DICE chain",
            ),
            (
                Event { tag: "CCEL".to_string(), event: None }.encode_to_vec(),
                "verifying DICE chain",
            ),
            (encode_event("CCEL", BYTES_VALUE_TYPE_URL, vec![0x08, 0x01]), "verifying DICE chain"),
            (fixture.ccel_event.clone(), "duplicate non-layer transparent event: CCEL"),
            (fixture.ccel_table_event.clone(), "duplicate non-layer transparent event: CCELTable"),
        ];
        for (extra_event, expected) in pushed_cases {
            let mut bad = fixture.evidence.clone();
            bad.transparent_event_log.as_mut().unwrap().encoded_events.push(extra_event);
            expect_synthetic_err(
                &verifier,
                &fixture.platform_results,
                &bad,
                &fixture.endorsements,
                expected,
            );
        }

        let mut missing_log = fixture.evidence.clone();
        missing_log.transparent_event_log = None;
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &missing_log,
            &fixture.endorsements,
            "no transparent event log",
        );
    }

    #[test]
    fn tdx_transparent_verify_after_platform_enforces_dice_hashes_and_all_layer_policies() {
        let fixture = build_tdx_transparent_fixture();
        let verifier = make_verifier(&fixture.reference_values);

        let mut bad_l1 = fixture.evidence.clone();
        bad_l1.transparent_event_log.as_mut().unwrap().encoded_events[1] = encode_event(
            "layer1Transparent",
            "type.googleapis.com/oak.attestation.v1.CbLayer1TransparentEvent",
            CbLayer1TransparentEvent {
                runtime_agent_binary_measurement: vec![0x99u8; 32],
                userspace_measurement: vec![0x22u8; 32],
                ..Default::default()
            }
            .encode_to_vec(),
        );
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &bad_l1,
            &fixture.endorsements,
            "event log hash mismatch",
        );

        let mut bad_l2 = fixture.evidence.clone();
        bad_l2.transparent_event_log.as_mut().unwrap().encoded_events[4] = encode_event(
            "layer2Transparent",
            "type.googleapis.com/oak.attestation.v1.CbLayer2TransparentEvent",
            CbLayer2TransparentEvent {
                packages: vec![MpmPackage {
                    mpm_version_id: "tampered/9.9".to_string(),
                    ..Default::default()
                }],
            }
            .encode_to_vec(),
        );
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &bad_l2,
            &fixture.endorsements,
            "event log hash mismatch",
        );

        let layer_cases: &[(&str, CbtMutator)] = &[
            ("verifying event log", |cbt| {
                cbt.kernel_layer.as_mut().unwrap().acpi = None;
            }),
            ("comparing runtime agent binary measurement", |cbt| {
                cbt.layer1.as_mut().unwrap().runtime_agent_binary =
                    Some(digest_brv(vec![0x99u8; 32], vec![]));
            }),
            ("could not be verified", |cbt| {
                cbt.layer2.as_mut().unwrap().binary_mpms = vec![MpmReferenceValue {
                    r#type: Some(mpm_reference_value::Type::Versions(MpmVersionIds {
                        versions: vec!["other/2.0".to_string()],
                    })),
                }];
            }),
        ];
        for (expected, mutate) in layer_cases {
            let mut rvs = fixture.reference_values.clone();
            if let Some(reference_values::Type::Cbt(cbt)) = rvs.r#type.as_mut() {
                mutate(cbt);
            }
            expect_synthetic_err(
                &make_verifier(&rvs),
                &fixture.platform_results,
                &fixture.evidence,
                &fixture.endorsements,
                expected,
            );
        }
    }

    #[test]
    fn tdx_transparent_verify_after_platform_rejects_user_data_firmware_and_missing_initial() {
        let fixture = build_tdx_transparent_fixture();
        let verifier = make_verifier(&fixture.reference_values);

        let mut missing_initial = fixture.endorsements.clone();
        missing_initial.initial = None;
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &fixture.evidence,
            &missing_initial,
            "no firmware endorsement",
        );

        let (other_priv, _) = generate_ecdsa_key_pair();
        let mut wrong_signer = fixture.evidence.clone();
        wrong_signer.signed_user_data_certificate =
            build_signed_user_data_cert(&other_priv, b"tdx-user-data");
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &wrong_signer,
            &fixture.endorsements,
            "verifying signed user data certificate",
        );

        let mut flipped = fixture.evidence.clone();
        let valid_cert = build_signed_user_data_cert(&fixture.final_layer_key, b"tdx-user-data");
        let last = valid_cert.len() - 1;
        flipped.signed_user_data_certificate = valid_cert;
        flipped.signed_user_data_certificate[last] ^= 0x01;
        expect_synthetic_err(
            &verifier,
            &fixture.platform_results,
            &flipped,
            &fixture.endorsements,
            "verifying signed user data certificate",
        );

        let mut bad_platform_results = EventAttestationResults::default();
        set_initial_measurement(&mut bad_platform_results, &[0x99u8; 48]);
        expect_synthetic_err(
            &verifier,
            &bad_platform_results,
            &fixture.evidence,
            &fixture.endorsements,
            "verifying firmware policy",
        );
    }
}
