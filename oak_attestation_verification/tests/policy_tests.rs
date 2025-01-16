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

use anyhow::Context;
use oak_attestation_verification::policy::{
    application::ApplicationPolicy, container::ContainerPolicy, firmware::FirmwarePolicy,
    kernel::KernelPolicy, platform::AmdSevSnpPolicy, system::SystemPolicy,
};
use oak_attestation_verification_types::policy::Policy;
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, endorsements, kernel_binary_reference_value, reference_values,
        text_reference_value, AmdSevSnpEndorsement, BinaryReferenceValue, CbReferenceValues,
        Endorsements, Evidence, FirmwareEndorsement, KernelBinaryReferenceValue,
        KernelLayerReferenceValues, OakContainersReferenceValues,
        OakRestrictedKernelReferenceValues, ReferenceValues, SkipVerification, TextReferenceValue,
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

const CB_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/cb_evidence_20250124.binarypb";
const CB_ENDORSEMENTS_PATH: &str =
    "oak_attestation_verification/testdata/cb_endorsements_20250124.binarypb";
const CB_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/cb_reference_values_20250124.binarypb";

const KERNEL_EVENT_INDEX: usize = 0;
const RK_APPLICATION_EVENT_INDEX: usize = 1;
const SYSTEM_EVENT_INDEX: usize = 1;
const CONTAINER_EVENT_INDEX: usize = 2;

// Pretend the tests run at this time: 15 Jan 2025, 12:00 UTC.
const MILLISECONDS_SINCE_EPOCH: i64 = 1736942400000;

fn extract_attestation_report(evidence: &Evidence) -> anyhow::Result<&AttestationReport> {
    let root_layer =
        &evidence.root_layer.as_ref().context("root DICE layer wasn't provided in the evidence")?;
    AttestationReport::ref_from(&root_layer.remote_attestation_report)
        .context("invalid AMD SEV-SNP attestation report")
}

// Loads a valid AMD SEV-SNP evidence instance for Oak Containers.
fn load_oc_evidence() -> Evidence {
    let serialized = fs::read(data_path(OC_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Loads a valid AMD SEV-SNP endorsements instance for Oak Containers.
fn load_oc_endorsements() -> Endorsements {
    let serialized =
        fs::read(data_path(OC_ENDORSEMENTS_PATH)).expect("could not read endorsements");
    Endorsements::decode(serialized.as_slice()).expect("could not decode endorsements")
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
fn load_rk_endorsements() -> Endorsements {
    let serialized =
        fs::read(data_path(RK_ENDORSEMENTS_PATH)).expect("could not read endorsements");
    Endorsements::decode(serialized.as_slice()).expect("could not decode endorsements")
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

fn load_cb_evidence() -> Evidence {
    let serialized = fs::read(data_path(CB_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

fn load_cb_endorsements() -> Endorsements {
    let serialized =
        fs::read(data_path(CB_ENDORSEMENTS_PATH)).expect("could not read endorsements");
    Endorsements::decode(serialized.as_slice()).expect("could not decode endorsements")
}

fn load_cb_reference_values() -> CbReferenceValues {
    let serialized =
        fs::read(data_path(CB_REFERENCE_VALUES_PATH)).expect("could not read reference values");
    let reference_values =
        ReferenceValues::decode(serialized.as_slice()).expect("could not decode reference values");
    let containers_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::Cb(containers_reference_values)) => {
            containers_reference_values.clone()
        }
        _ => panic!("couldn't find CB reference values"),
    };
    assert!(containers_reference_values.root_layer.is_some());
    assert!(containers_reference_values.root_layer.as_ref().unwrap().amd_sev.is_some());
    assert!(containers_reference_values.kernel_layer.is_some());
    assert!(containers_reference_values.system_layer.is_some());
    assert!(containers_reference_values.application_layer.is_some());
    containers_reference_values
}

lazy_static::lazy_static! {
    static ref OC_EVIDENCE: Evidence = load_oc_evidence();
    static ref OC_ENDORSEMENTS: Endorsements = load_oc_endorsements();
    static ref OC_REFERENCE_VALUES: OakContainersReferenceValues = load_oc_reference_values();

    static ref RK_EVIDENCE: Evidence = load_rk_evidence();
    static ref RK_ENDORSEMENTS: Endorsements = load_rk_endorsements();
    static ref RK_REFERENCE_VALUES: OakRestrictedKernelReferenceValues = load_rk_reference_values();

    static ref CB_EVIDENCE: Evidence = load_cb_evidence();
    static ref CB_ENDORSEMENTS: Endorsements = load_cb_endorsements();
    static ref CB_REFERENCE_VALUES: CbReferenceValues = load_cb_reference_values();
}

#[test]
fn amd_sev_snp_platform_policy_verify_succeeds() {
    let platform_reference_values =
        OC_REFERENCE_VALUES.root_layer.as_ref().unwrap().amd_sev.as_ref().unwrap();
    let policy = AmdSevSnpPolicy::new(platform_reference_values);
    let attestation_report = extract_attestation_report(&OC_EVIDENCE).unwrap();
    let endorsement = AmdSevSnpEndorsement {
        tee_certificate: match OC_ENDORSEMENTS.r#type.as_ref() {
            Some(endorsements::Type::OakContainers(e)) => {
                e.root_layer.as_ref().unwrap().tee_certificate.to_vec()
            }
            _ => vec![],
        },
    };

    let result = policy.verify(attestation_report, &endorsement.into(), MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
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

    let result =
        policy.verify(firmware_measurement, &firmware_endorsement.into(), MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_kernel_policy_verify_succeeds() {
    let reference_values = OC_REFERENCE_VALUES.kernel_layer.as_ref().unwrap();
    let policy = KernelPolicy::new(reference_values);
    let event = &OC_EVIDENCE.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
    let endorsement = &OC_ENDORSEMENTS.events[KERNEL_EVENT_INDEX];

    let result = policy.verify(event, endorsement, MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_system_policy_verify_succeeds() {
    let event_reference_values = OC_REFERENCE_VALUES.system_layer.as_ref().unwrap();
    let policy = SystemPolicy::new(event_reference_values);
    let event = &OC_EVIDENCE.event_log.as_ref().unwrap().encoded_events[SYSTEM_EVENT_INDEX];
    let endorsement = &OC_ENDORSEMENTS.events[SYSTEM_EVENT_INDEX];

    let result = policy.verify(event, endorsement, MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn oc_container_policy_verify_succeeds() {
    // TODO: b/382550581 - Container reference values currently skip verification.
    let event_reference_values = OC_REFERENCE_VALUES.container_layer.as_ref().unwrap();
    let policy = ContainerPolicy::new(event_reference_values);
    let event = &OC_EVIDENCE.event_log.as_ref().unwrap().encoded_events[CONTAINER_EVENT_INDEX];
    let endorsement = &OC_ENDORSEMENTS.events[CONTAINER_EVENT_INDEX];

    let result = policy.verify(event, endorsement, MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn rk_kernel_policy_verify_succeeds() {
    let reference_values = RK_REFERENCE_VALUES.kernel_layer.as_ref().unwrap();
    let policy = KernelPolicy::new(reference_values);
    let event = &RK_EVIDENCE.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
    let endorsement = &RK_ENDORSEMENTS.events[KERNEL_EVENT_INDEX];

    let result = policy.verify(event, endorsement, MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn rk_application_policy_verify_succeeds() {
    // TODO: b/382550581 - Application reference values currently skip verification.
    let reference_values = RK_REFERENCE_VALUES.application_layer.as_ref().unwrap();
    let policy = ApplicationPolicy::new(reference_values);
    let event = &RK_EVIDENCE.event_log.as_ref().unwrap().encoded_events[RK_APPLICATION_EVENT_INDEX];
    let endorsement = &RK_ENDORSEMENTS.events[RK_APPLICATION_EVENT_INDEX];

    let result = policy.verify(event, endorsement, MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}

#[test]
fn cb_kernel_policy_verify_succeeds() {
    // TODO: b/388251723 - Use real CB reference values instead of [`Skip`].
    let _reference_values = CB_REFERENCE_VALUES.kernel_layer.as_ref().unwrap();
    let kernel_skip = KernelBinaryReferenceValue {
        r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
    };
    let text_skip =
        TextReferenceValue { r#type: Some(text_reference_value::Type::Skip(SkipVerification {})) };
    let binary_skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };
    let skip_reference_values = KernelLayerReferenceValues {
        kernel: Some(kernel_skip),
        kernel_cmd_line_text: Some(text_skip),
        init_ram_fs: Some(binary_skip.clone()),
        memory_map: Some(binary_skip.clone()),
        acpi: Some(binary_skip),
    };

    let policy = KernelPolicy::new(&skip_reference_values);
    let event = &CB_EVIDENCE.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
    let endorsement = Variant::default();

    let result = policy.verify(event, &endorsement, MILLISECONDS_SINCE_EPOCH);

    // TODO: b/356631062 - Verify detailed attestation results.
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
}
