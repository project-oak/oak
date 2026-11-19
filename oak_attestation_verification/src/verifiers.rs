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

    use coset::CborSerializable;
    use oak_dice::cert::{generate_ecdsa_key_pair, verifying_key_to_cose_key};
    use oak_proto_rust::oak::attestation::v1::{
        BinaryReferenceValue, CbLayer1TransparentReferenceValues,
        CbLayer2TransparentReferenceValues, CbTransparentReferenceValues, IntelTdxReferenceValues,
        KernelLayerReferenceValues, RootLayerReferenceValues, SkipVerification,
        TdxTcbSvnReferenceValue, TeePlatform, binary_reference_value, tdx_tcb_svn_reference_value,
    };
    use oak_time::{clock::FixedClock, make_instant};
    use prost_types::Any;
    use test_util::AttestationData;

    use super::*;

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
}
