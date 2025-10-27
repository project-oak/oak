//
// Copyright 2024 The Project Oak Authors
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

//! Tests for policy-based attestation verification.

use core::iter::Iterator;
use std::{fs, sync::Arc};

use oak_attestation_verification::{
    create_amd_verifier, create_insecure_verifier, create_intel_tdx_verifier,
    verifier::{verify_dice_chain_and_extract_evidence, SoftwareRootedDiceAttestationVerifier},
    AmdSevSnpDiceAttestationVerifier, AmdSevSnpPolicy, ContainerPolicy, FirmwarePolicy,
    IntelTdxAttestationVerifier, IntelTdxPolicy, KernelPolicy, SystemPolicy,
};
use oak_attestation_verification_types::{policy::EventPolicy, verifier::AttestationVerifier};
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results, binary_reference_value, endorsements, AmdSevSnpEndorsement,
        AttestationResults, Endorsements, Evidence, ReferenceValues, SkipVerification,
    },
    Variant,
};
use oak_time::{clock::FixedClock, Instant};
use prost::Message;
use test_util::{
    allow_insecure, create_reference_values_for_extracted_evidence, get_cb_reference_values,
    manipulate::{
        get_acpi_rv, get_init_ram_fs_rv, get_kernel_cmd_line_rv, get_kernel_rv, get_oc_config_rv,
        get_oc_container_rv, get_oc_system_image_rv, get_rk_application_rv, get_rk_config_rv,
        get_stage0_rv, manipulate_kernel_cmd_line, manipulate_kernel_image,
        manipulate_kernel_setup_data, manipulate_sha2_256, manipulate_sha2_384,
    },
    AttestationData,
};

use crate::attestation_results::Status;

const CB_EVIDENCE_SR_PATH: &str =
    "oak_attestation_verification/testdata/cb_evidence_software_rooted.binarypb";

// A random time value used to parametrize test cases.
const TEST_TIME: Instant = Instant::from_unix_millis(1_000_000);

// Helper which asserts success of the verification call.
fn assert_success(result: anyhow::Result<AttestationResults>) {
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());

    let proto = result.as_ref().unwrap();
    if proto.status() != Status::Success {
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(proto.status() == Status::Success);
}

// Helper which asserts failure of the verification call.
fn assert_failure(result: anyhow::Result<AttestationResults>) {
    if result.is_ok() {
        let proto = result.as_ref().unwrap();
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(result.is_err(), "Expected failure but got success: {:?}", result);
}

// Shorthand that produces digest-based reference values from evidence.
fn make_reference_values(evidence: &Evidence) -> ReferenceValues {
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(evidence).expect("invalid DICE evidence");
    create_reference_values_for_extracted_evidence(extracted_evidence)
}

fn load_cb_evidence_software_rooted() -> Evidence {
    let serialized = fs::read(data_path(CB_EVIDENCE_SR_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

#[test]
fn cb_software_rooted_dice_verify_succeeds() {
    let clock = FixedClock::at_instant(TEST_TIME);
    let evidence = load_cb_evidence_software_rooted();
    let endorsements = Endorsements::default();

    let verifier = SoftwareRootedDiceAttestationVerifier::new(Arc::new(clock));

    let result = verifier.verify(&evidence, &endorsements);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn cb_dice_verify_succeeds() {
    let d = AttestationData::load_cb();
    let clock = FixedClock::at_instant(d.make_valid_time());
    let ref_values = get_cb_reference_values(&d.reference_values);
    let platform_endorsement = AmdSevSnpEndorsement {
        tee_certificate: match d.endorsements.r#type.as_ref() {
            Some(endorsements::Type::Cb(e)) => {
                e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
            }
            _ => vec![],
        },
    };
    let empty_variant: Variant = Variant::default();
    let endorsements = Endorsements {
        platform: Some(platform_endorsement.into()),
        initial: Some(empty_variant),
        ..Default::default()
    };

    let platform_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
    let platform_policy = AmdSevSnpPolicy::new(platform_reference_values);

    let firmware_reference_values =
        ref_values.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap().stage0.as_ref().unwrap();
    // TODO: b/375137648 - Use real reference once new endorsements are available.
    let mut skip_firmware_reference_values = firmware_reference_values.clone();
    skip_firmware_reference_values.r#type =
        Some(binary_reference_value::Type::Skip(SkipVerification {}));
    let firmware_policy = FirmwarePolicy::new(&skip_firmware_reference_values);

    let event_policies: Vec<Box<dyn EventPolicy>> = vec![];

    let verifier = AmdSevSnpDiceAttestationVerifier::new(
        platform_policy,
        Box::new(firmware_policy),
        event_policies,
        Arc::new(clock),
    );

    let result = verifier.verify(&d.evidence, &endorsements);
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn tdx_oc_verify_succeeds() {
    let d = AttestationData::load_tdx_oc();
    let clock: FixedClock = FixedClock::at_instant(d.make_valid_time());
    let verifier = create_intel_tdx_verifier(clock, &d.reference_values).expect("no verifier");
    assert_success(verifier.verify(&d.evidence, &d.endorsements));
}

#[test]
fn tdx_oc_generated_reference_values_verify_succeeds() {
    let d = AttestationData::load_tdx_oc();
    let clock = Arc::new(FixedClock::at_instant(d.make_valid_time()));
    let evidence = d.evidence;

    let (platform_rv, firmware_rv) = IntelTdxPolicy::evidence_to_reference_values(
        evidence.root_layer.as_ref().expect("no root layer evidence"),
    )
    .expect("invalid root layer evidence");
    let platform_policy = IntelTdxPolicy::new(&platform_rv);
    let firmware_policy = Box::new(FirmwarePolicy::new(&firmware_rv));

    let mut events =
        evidence.event_log.as_ref().expect("no event log").encoded_events.as_slice().iter();
    let kernel_policy = Box::new(KernelPolicy::new(
        &KernelPolicy::evidence_to_reference_values(events.next().expect("no kernel event"))
            .expect("invalid kernel event"),
    ));
    let system_policy = Box::new(SystemPolicy::new(
        &SystemPolicy::evidence_to_reference_values(events.next().expect("no system event"))
            .expect("invalid system event"),
    ));
    let container_policy = Box::new(ContainerPolicy::new(
        &ContainerPolicy::evidence_to_reference_values(events.next().expect("no container event"))
            .expect("invalid container event"),
    ));
    let event_policies: Vec<Box<dyn EventPolicy>> =
        vec![kernel_policy, system_policy, container_policy];
    let verifier =
        IntelTdxAttestationVerifier::new(platform_policy, firmware_policy, event_policies, clock);
    assert_success(verifier.verify(&evidence, &d.endorsements));
}

fn verify_amd(
    timestamp: Instant,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<AttestationResults> {
    let clock = FixedClock::at_instant(timestamp);
    let v = create_amd_verifier(clock, reference_values).expect("no verifier");
    v.verify(evidence, endorsements)
}

fn verify_insecure(
    timestamp: Instant,
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<AttestationResults> {
    let clock = FixedClock::at_instant(timestamp);
    let v = create_insecure_verifier(clock, reference_values).expect("no verifier");
    v.verify(evidence, endorsements)
}

macro_rules! verify_amd_success {
    ($($name:tt)*) => {
        mod verify_amd_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    assert_success(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_amd_success! {
    load_milan_oc_release
    load_milan_oc_staging
    // Requires event-based endorsements for both. Enable once we have them.
    // (Applies everywhere.)
    // load_genoa_oc
    // load_turin_oc
    load_milan_rk_release
    load_milan_rk_staging
}

// Some samples cannot be verified with the AMD verifier.
macro_rules! verify_amd_failure {
    ($($name:tt)*) => {
        mod verify_amd_failure {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    assert_failure(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_amd_failure! {
    load_fake
}

macro_rules! verify_amd_success_explicit_reference_values {
    ($($name:tt)*) => {
        mod verify_amd_success_explicit_reference_values {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    let reference_values = make_reference_values(&d.evidence);
                    assert_success(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &reference_values));
                }
            )*
        }
    }
}

verify_amd_success_explicit_reference_values! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
}

macro_rules! verify_amd_manipulated_root_public_key_failure {
    ($($name:tt)*) => {
        mod verify_amd_manipulated_root_public_key_failure {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();
                    d.evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
                    assert_failure(verify_amd(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_amd_manipulated_root_public_key_failure! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
}

macro_rules! verify_insecure_success {
    ($($name:tt)*) => {
        mod verify_insecure_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();
                    allow_insecure(&mut d.reference_values);
                    assert_success(verify_insecure(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_insecure_success! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_fake
}

macro_rules! verify_insecure_manipulated_root_public_key_failure {
    ($($name:tt)*) => {
        mod verify_insecure_manipulated_root_public_key_failure {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();
                    allow_insecure(&mut d.reference_values);
                    d.evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
                    assert_failure(verify_insecure(d.make_valid_time(), &d.evidence, &d.endorsements, &d.reference_values));
                }
            )*
        }
    }
}

verify_insecure_manipulated_root_public_key_failure! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_fake
}

// Macro that creates many tests that observe failure after manipulating
// reference values of a working attestation sample.
macro_rules! manipulate_tests {
    ($module_name:tt, $get_fn:tt, $manip_fn:tt, $verify_fn:tt, $($load_name:tt, )*) => {
        mod $module_name {
            use super::*;

            $(
                #[test]
                fn $load_name() {
                    let d = AttestationData::$load_name();
                    let mut rvs = make_reference_values(&d.evidence);
                    let rv = $get_fn(&mut rvs);
                    $manip_fn(rv);

                    assert_failure($verify_fn(
                        d.make_valid_time(),
                        &d.evidence,
                        &d.endorsements,
                        &rvs,
                    ));
                }
            )*
        }
    }
}

manipulate_tests! {
    amd_stage0_manipulate_digests_failure,
    get_stage0_rv, manipulate_sha2_384, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_init_ram_fs_manipulate_digests_failure,
    get_init_ram_fs_rv, manipulate_sha2_256, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_acpi_manipulate_digests_failure,
    get_acpi_rv, manipulate_sha2_256, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_kernel_image_manipulate_digests_failure,
    get_kernel_rv, manipulate_kernel_image, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_kernel_setup_data_manipulate_digests_failure,
    get_kernel_rv, manipulate_kernel_setup_data, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_kernel_cmd_line_manipulate_value_failure,
    get_kernel_cmd_line_rv, manipulate_kernel_cmd_line, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_oc_system_image_manipulate_digests_failure,
    get_oc_system_image_rv, manipulate_sha2_256, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_oc_container_manipulate_digests_failure,
    get_oc_container_rv, manipulate_sha2_256, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_oc_config_manipulate_digests_failure,
    get_oc_config_rv, manipulate_sha2_256, verify_amd,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_rk_application_manipulate_digests_failure,
    get_rk_application_rv, manipulate_sha2_256, verify_amd,
    load_milan_rk_release,
    load_milan_rk_staging,
}

manipulate_tests! {
    amd_rk_config_manipulate_digests_failure,
    get_rk_config_rv, manipulate_sha2_256, verify_amd,
    load_milan_rk_release,
    load_milan_rk_staging,
}
