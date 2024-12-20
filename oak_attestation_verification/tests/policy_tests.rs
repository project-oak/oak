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

use std::fs;

use anyhow::{anyhow, Context};
use oak_attestation_verification::policy::{
    application::ApplicationPolicy, container::ContainerPolicy, firmware::FirmwarePolicy,
    kernel::KernelPolicy, platform::AmdSevSnpPolicy, system::SystemPolicy,
};
use oak_attestation_verification_types::{
    policy::Policy, AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID, APPLICATION_ENDORSEMENT_ID,
    CONTAINER_ENDORSEMENT_ID, FIRMWARE_ENDORSEMENT_ID, KERNEL_ENDORSEMENT_ID,
    SYSTEM_ENDORSEMENT_ID,
};
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, endorsements, reference_values, AmdSevSnpEndorsement, Endorsements,
        Evidence, FirmwareEndorsement, OakContainersEndorsements, OakContainersReferenceValues,
        OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
        SkipVerification,
    },
    Variant,
};
use oak_sev_snp_attestation_report::AttestationReport;
use prost::Message;
use zerocopy::FromBytes;

const OC_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/oc_evidence_20241205.binarypb";
const OC_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/oc_endorsements_20241205.binarypb";
const OC_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/oc_reference_values_20241205.binarypb";

const RK_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/rk_evidence_20241205.binarypb";
const RK_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/rk_endorsements_20241205.binarypb";
const RK_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/rk_reference_values_20241205.binarypb";

const KERNEL_EVENT_INDEX: usize = 0;
const RK_APPLICATION_EVENT_INDEX: usize = 1;
const SYSTEM_EVENT_INDEX: usize = 1;
const CONTAINER_EVENT_INDEX: usize = 2;

// Pretend the tests run at this time: 5 Dec 2024, 12:00 UTC.
const MILLISECONDS_SINCE_EPOCH: i64 = 1733400000000;

fn extract_attestation_report(evidence: &Evidence) -> anyhow::Result<&AttestationReport> {
    let root_layer =
        &evidence.root_layer.as_ref().context("root DICE layer wasn't provided in the evidence")?;
    AttestationReport::ref_from(&root_layer.remote_attestation_report)
        .context("invalid AMD SEV-SNP attestation report")
}

fn extract_event(evidence: &Evidence, index: usize) -> anyhow::Result<Vec<u8>> {
    if let Some(event_log) = &evidence.event_log {
        if event_log.encoded_events.len() < index + 1 {
            anyhow::bail!(
                "not enough events, expected at least {}, found {}",
                index + 1,
                event_log.encoded_events.len()
            );
        }
        Ok(event_log.encoded_events[index].clone())
    } else {
        Err(anyhow!("event log wasn't provided in the evidence"))
    }
}

// Loads a valid AMD SEV-SNP evidence instance for Oak Containers.
fn load_oc_evidence() -> Evidence {
    let serialized = fs::read(data_path(OC_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Loads a valid AMD SEV-SNP endorsements instance for Oak Containers.
fn load_oc_endorsements() -> OakContainersEndorsements {
    let serialized =
        fs::read(data_path(OC_ENDORSEMENTS_PATH)).expect("could not read endorsements");
    let endorsements =
        Endorsements::decode(serialized.as_slice()).expect("could not decode endorsements");
    let containers_endorsements = match endorsements.r#type.as_ref() {
        Some(endorsements::Type::OakContainers(containers_endorsements)) => {
            containers_endorsements.clone()
        }
        _ => panic!("couldn't find Oak Containers reference values"),
    };
    assert!(containers_endorsements.root_layer.is_some());
    assert!(containers_endorsements.kernel_layer.is_some());
    assert!(containers_endorsements.system_layer.is_some());
    // TODO: b/368030563 - Verify container layer once corresponding endorsements
    // are provided. assert!(containers_endorsements.container_layer.is_some());
    containers_endorsements
}

// Loads valid AMD SEV-SNP reference values instance for Oak Containers.
fn load_oc_reference_values() -> OakContainersReferenceValues {
    let serialized =
        fs::read(data_path(OC_REFERENCE_VALUES_PATH)).expect("could not read reference values");
    let reference_values =
        ReferenceValues::decode(serialized.as_slice()).expect("could not decode reference values");
    let containers_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(containers_reference_values)) => {
            containers_reference_values.clone()
        }
        _ => panic!("couldn't find Oak Containers reference values"),
    };
    assert!(containers_reference_values.root_layer.is_some());
    assert!(containers_reference_values.root_layer.as_ref().unwrap().amd_sev.is_some());
    assert!(containers_reference_values.kernel_layer.is_some());
    assert!(containers_reference_values.system_layer.is_some());
    assert!(containers_reference_values.container_layer.is_some());
    containers_reference_values
}

// Loads a valid AMD SEV-SNP evidence instance for Oak Restricted Kernel.
fn load_rk_evidence() -> Evidence {
    let serialized = fs::read(data_path(RK_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Loads a valid AMD SEV-SNP endorsements instance for Oak Restricted Kernel.
fn load_rk_endorsements() -> OakRestrictedKernelEndorsements {
    let serialized =
        fs::read(data_path(RK_ENDORSEMENTS_PATH)).expect("could not read endorsements");
    let endorsements =
        Endorsements::decode(serialized.as_slice()).expect("could not decode endorsements");
    let rk_endorsements = match endorsements.r#type.as_ref() {
        Some(endorsements::Type::OakRestrictedKernel(rk_endorsements)) => rk_endorsements.clone(),
        _ => panic!("couldn't find Oak RestrictedKernel reference values"),
    };
    assert!(rk_endorsements.root_layer.is_some());
    assert!(rk_endorsements.kernel_layer.is_some());
    assert!(rk_endorsements.application_layer.is_some());
    rk_endorsements
}

// Loads valid AMD SEV-SNP reference values instance for Oak Restricted Kernel.
fn load_rk_reference_values() -> OakRestrictedKernelReferenceValues {
    let serialized =
        fs::read(data_path(RK_REFERENCE_VALUES_PATH)).expect("could not read reference values");
    let reference_values =
        ReferenceValues::decode(serialized.as_slice()).expect("could not decode reference values");
    let rk_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakRestrictedKernel(rk_reference_values)) => {
            rk_reference_values.clone()
        }
        _ => panic!("couldn't find Oak RestrictedKernel reference values"),
    };
    assert!(rk_reference_values.root_layer.is_some());
    assert!(rk_reference_values.kernel_layer.is_some());
    assert!(rk_reference_values.application_layer.is_some());
    rk_reference_values
}

lazy_static::lazy_static! {
    static ref OC_EVIDENCE: Evidence = load_oc_evidence();
    static ref OC_ENDORSEMENTS: OakContainersEndorsements = load_oc_endorsements();
    static ref OC_REFERENCE_VALUES: OakContainersReferenceValues = load_oc_reference_values();

    static ref RK_EVIDENCE: Evidence = load_rk_evidence();
    static ref RK_ENDORSEMENTS: OakRestrictedKernelEndorsements = load_rk_endorsements();
    static ref RK_REFERENCE_VALUES: OakRestrictedKernelReferenceValues = load_rk_reference_values();
}

#[test]
fn amd_sev_snp_platform_policy_verify_succeeds() {
    let platform_reference_values =
        OC_REFERENCE_VALUES.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
    let policy = AmdSevSnpPolicy::new(platform_reference_values);

    let attestation_report = extract_attestation_report(&OC_EVIDENCE).unwrap();
    // TODO: b/375137648 - Use new endorsements directly once they are available.
    let platform_endorsement = AmdSevSnpEndorsement {
        tee_certificate: OC_ENDORSEMENTS.root_layer.as_ref().unwrap().tee_certificate.to_vec(),
    };
    let encoded_endorsement = Variant {
        id: AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID.to_vec(),
        value: platform_endorsement.encode_to_vec(),
    };

    let result = policy.verify(attestation_report, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}

#[test]
fn amd_sev_snp_firmware_policy_verify_succeeds() {
    let firmware_reference_values = OC_REFERENCE_VALUES
        .root_layer
        .as_ref()
        .unwrap()
        .amd_sev
        .as_ref()
        .unwrap()
        .stage0
        .as_ref()
        .unwrap();
    // TODO: b/375137648 - Use real reference once new endorsements are available.
    let mut skip_firmware_reference_values = firmware_reference_values.clone();
    skip_firmware_reference_values.r#type =
        Some(binary_reference_value::Type::Skip(SkipVerification {}));
    let policy = FirmwarePolicy::new(&skip_firmware_reference_values);

    let firmware_measurement = &extract_attestation_report(&OC_EVIDENCE).unwrap().data.measurement;
    // TODO: b/375137648 - Use new endorsements directly once available.
    let firmware_endorsement = FirmwareEndorsement { firmware: None };
    let encoded_endorsement = Variant {
        id: FIRMWARE_ENDORSEMENT_ID.to_vec(),
        value: firmware_endorsement.encode_to_vec(),
    };

    let result =
        policy.verify(firmware_measurement, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}

#[test]
fn oc_kernel_policy_verify_succeeds() {
    let event_reference_values = OC_REFERENCE_VALUES.kernel_layer.as_ref().unwrap();
    let policy = KernelPolicy::new(event_reference_values);

    let event = extract_event(&OC_EVIDENCE, KERNEL_EVENT_INDEX).expect("couldn't extract event");
    let endorsement = OC_ENDORSEMENTS.kernel_layer.as_ref().unwrap();

    // TODO: b/375137648 - Populate `events` proto field.
    let encoded_endorsement =
        Variant { id: KERNEL_ENDORSEMENT_ID.to_vec(), value: endorsement.encode_to_vec() };

    let result = policy.verify(&event, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}

#[test]
fn oc_system_policy_verify_succeeds() {
    let event_reference_values = OC_REFERENCE_VALUES.system_layer.as_ref().unwrap();
    let policy = SystemPolicy::new(event_reference_values);

    let event = extract_event(&OC_EVIDENCE, SYSTEM_EVENT_INDEX).expect("couldn't extract event");
    let endorsement = OC_ENDORSEMENTS.system_layer.as_ref().unwrap();

    // TODO: b/375137648 - Populate `events` proto field.
    let encoded_endorsement =
        Variant { id: SYSTEM_ENDORSEMENT_ID.to_vec(), value: endorsement.encode_to_vec() };

    let result = policy.verify(&event, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}

#[test]
fn oc_container_policy_verify_succeeds() {
    // TODO: b/382550581 - Container reference values currently skip verification.
    let event_reference_values = OC_REFERENCE_VALUES.container_layer.as_ref().unwrap();
    let policy = ContainerPolicy::new(event_reference_values);

    let event = extract_event(&OC_EVIDENCE, CONTAINER_EVENT_INDEX).expect("couldn't extract event");
    // TODO: b/382550581 - Use real endorsements once they provide an application
    // level endorsement. let endorsement =
    // OC_ENDORSEMENTS.container_layer.as_ref().unwrap();
    let endorsement = std::vec![];

    // TODO: b/375137648 - Populate `events` proto field.
    let encoded_endorsement =
        Variant { id: CONTAINER_ENDORSEMENT_ID.to_vec(), value: endorsement.encode_to_vec() };

    let result = policy.verify(&event, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}

#[test]
fn rk_kernel_policy_verify_succeeds() {
    let event_reference_values = RK_REFERENCE_VALUES.kernel_layer.as_ref().unwrap();
    let policy = KernelPolicy::new(event_reference_values);

    let event = extract_event(&RK_EVIDENCE, KERNEL_EVENT_INDEX).expect("couldn't extract event");
    let endorsement = RK_ENDORSEMENTS.kernel_layer.as_ref().unwrap();

    // TODO: b/375137648 - Populate `events` proto field.
    let encoded_endorsement =
        Variant { id: KERNEL_ENDORSEMENT_ID.to_vec(), value: endorsement.encode_to_vec() };

    let result = policy.verify(&event, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}

#[test]
fn rk_application_policy_verify_succeeds() {
    // TODO: b/382550581 - Application reference values currently skip verification.
    let event_reference_values = RK_REFERENCE_VALUES.application_layer.as_ref().unwrap();
    let policy = ApplicationPolicy::new(event_reference_values);

    let event =
        extract_event(&RK_EVIDENCE, RK_APPLICATION_EVENT_INDEX).expect("couldn't extract event");
    let endorsement = RK_ENDORSEMENTS.application_layer.as_ref().unwrap();

    // TODO: b/375137648 - Populate `events` proto field.
    let encoded_endorsement =
        Variant { id: APPLICATION_ENDORSEMENT_ID.to_vec(), value: endorsement.encode_to_vec() };

    let result = policy.verify(&event, &encoded_endorsement, MILLISECONDS_SINCE_EPOCH);
    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok());
}
