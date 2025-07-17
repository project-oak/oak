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

use std::fs;

use oak_attestation_verification::{
    expect::get_expected_values,
    reference_values_from_evidence,
    verifier::{
        to_attestation_results, verify, verify_dice_chain_and_extract_evidence,
        verify_with_expected_values,
    },
};
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, binary_reference_value, extracted_evidence::EvidenceValues,
        kernel_binary_reference_value, reference_values, root_layer_data::Report,
        text_reference_value, BinaryReferenceValue, ContainerLayerEndorsements, Digests,
        Endorsements, Evidence, ExpectedValues, ExtractedEvidence, InsecureReferenceValues,
        KernelLayerEndorsements, OakContainersEndorsements, ReferenceValues, Regex,
        RootLayerEndorsements, RootLayerReferenceValues, SkipVerification, SystemLayerEndorsements,
        TcbVersion, TextReferenceValue,
    },
    RawDigest,
};
use prost::Message;
use test_util::{
    attestation_data::AttestationData,
    endorsement_data::EndorsementData,
    factory::{create_oc_reference_values, create_rk_reference_values},
};

// Fake attestation
const FAKE_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/fake_evidence.binarypb";
const FAKE_EXPECTED_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/fake_expected_values.binarypb";

// Legacy Restricted Kernel attestation
const RK_OBSOLETE_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/rk_evidence_20240312.binarypb";

// Pretend the tests run at this time: 1 March 2024, 12:00 UTC. This date must
// be valid with respect to the endorsement behind ENDORSEMENT_PATH.
const NOW_UTC_MILLIS: i64 = 1709294400000;

// Creates a valid AMD SEV-SNP evidence instance for a restricted kernel
// application but with obsolete DICE data that is still used by some clients.
fn create_rk_obsolete_evidence() -> Evidence {
    let serialized =
        fs::read(data_path(RK_OBSOLETE_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid fake evidence instance.
fn create_fake_evidence() -> Evidence {
    let serialized = fs::read(data_path(FAKE_EVIDENCE_PATH)).expect("could not read fake evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode fake evidence")
}

fn create_fake_expected_values() -> ExpectedValues {
    let serialized = fs::read(data_path(FAKE_EXPECTED_VALUES_PATH))
        .expect("could not read fake expected values");
    ExpectedValues::decode(serialized.as_slice()).expect("could not decode fake expected values")
}

// Creates mock endorsements for an Oak Containers chain.
fn create_oc_endorsements(vcek_cert: &[u8]) -> Endorsements {
    let d = EndorsementData::load();

    let root_layer = RootLayerEndorsements { tee_certificate: vcek_cert.to_vec(), stage0: None };
    let kernel_layer = KernelLayerEndorsements {
        kernel: None,
        kernel_cmd_line: None,
        // The testdata endorsement happens to be oak_orchestrator.
        init_ram_fs: Some(d.tr_endorsement),
        memory_map: None,
        acpi: None,
    };
    let system_layer = SystemLayerEndorsements { system_image: None };
    let container_layer = ContainerLayerEndorsements { binary: None, configuration: None };

    let ends = OakContainersEndorsements {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    Endorsements {
        r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(ends)),
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
    }
}

// Shorthand that produces digest-based reference values from evidence.
fn make_reference_values(evidence: &Evidence) -> ReferenceValues {
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(evidence).expect("invalid DICE evidence");
    reference_values_from_evidence(extracted_evidence)
}

// Helper which asserts success of the legacy verify() call.
fn assert_success(result: anyhow::Result<ExtractedEvidence>) {
    let proto = to_attestation_results(&result);

    if proto.status() != Status::Success {
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(result.is_ok());
    assert!(proto.status() == Status::Success);
}

// Helper which asserts failure of the legacy verify() call.
fn assert_failure(result: anyhow::Result<ExtractedEvidence>) {
    let proto = to_attestation_results(&result);

    if proto.status() == Status::Success {
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(result.is_err());
    assert!(proto.status() == Status::GenericFailure);
}

#[test]
fn verify_milan_oc_legacy_success() {
    let d = AttestationData::load_milan_oc_legacy();

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_milan_oc_legacy_explicit_reference_values() {
    let d = AttestationData::load_milan_oc_legacy();
    let reference_values = make_reference_values(&d.evidence);

    assert_success(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn verify_cb_succeeds() {
    let d = AttestationData::load_cb();

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_milan_rk_legacy_success() {
    let d = AttestationData::load_milan_rk_legacy();

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_rk_explicit_reference_values_success() {
    let d = AttestationData::load_milan_rk_legacy();
    let reference_values = make_reference_values(&d.evidence);

    assert_success(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn verify_fake_evidence_success() {
    let evidence = create_fake_evidence();
    let endorsements = AttestationData::load_milan_oc_legacy().endorsements;

    let mut reference_values = create_oc_reference_values();
    if let Some(reference_values::Type::OakContainers(reference)) = reference_values.r#type.as_mut()
    {
        reference.root_layer = Some(RootLayerReferenceValues {
            insecure: Some(InsecureReferenceValues {}),
            ..Default::default()
        });
    } else {
        panic!("invalid reference value type");
    }

    assert_success(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values));
}

#[test]
fn verify_fake_evidence_explicit_reference_values() {
    let evidence = create_fake_evidence();
    let endorsements = AttestationData::load_milan_oc_legacy().endorsements;
    let reference_values = make_reference_values(&evidence);

    assert_success(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values));
}

#[test]
fn verify_fake_evidence_split_verify_calls() {
    let evidence = create_fake_evidence();
    let endorsements = AttestationData::load_milan_oc_legacy().endorsements;
    let reference_values = make_reference_values(&evidence);
    let computed_expected_values =
        get_expected_values(NOW_UTC_MILLIS, &endorsements, &reference_values).unwrap();

    assert_success(verify_with_expected_values(
        NOW_UTC_MILLIS,
        &evidence,
        &endorsements,
        &computed_expected_values,
    ));
}

#[test]
fn verify_fake_evidence_explicit_reference_values_expected_values_correct() {
    let evidence = create_fake_evidence();

    let d = AttestationData::load_milan_oc_legacy();
    let vcek_cert = d.get_tee_certificate().expect("failed to get VCEK cert");
    let endorsements = create_oc_endorsements(&vcek_cert);

    let reference_values = make_reference_values(&evidence);

    let computed_expected_values =
        get_expected_values(NOW_UTC_MILLIS, &endorsements, &reference_values).unwrap();

    let mut buf = vec![];
    computed_expected_values
        .encode(&mut buf)
        .expect("Could not encode expected values from result");

    let expected_expected_values = create_fake_expected_values();

    assert!(computed_expected_values == expected_expected_values)
}

#[test]
fn verify_fails_with_manipulated_root_public_key() {
    let mut d = AttestationData::load_milan_oc_legacy();

    d.evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;

    assert_failure(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[allow(deprecated)]
#[test]
fn verify_fails_with_unsupported_tcb_version() {
    let mut d = AttestationData::load_milan_oc_legacy();

    let tcb_version = TcbVersion { boot_loader: 0, tee: 0, snp: u32::MAX, microcode: 0, fmc: 0 };
    match d.reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakContainers(rfs)) => {
            rfs.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().min_tcb_version =
                Some(tcb_version);
        }
        Some(_) => {}
        None => {}
    };

    assert_failure(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_succeeds_with_right_initial_measurement() {
    let mut d = AttestationData::load_milan_oc_legacy();

    let actual = if let Some(EvidenceValues::OakContainers(values)) =
        verify_dice_chain_and_extract_evidence(&d.evidence)
            .expect("invalid DICE chain")
            .evidence_values
            .as_ref()
    {
        if let Some(Report::SevSnp(report)) =
            values.root_layer.as_ref().expect("no root layer").report.as_ref()
        {
            Some(report.initial_measurement.clone())
        } else {
            None
        }
    } else {
        None
    }
    .expect("invalid DICE evidence");

    if let Some(reference_values::Type::OakContainers(reference)) =
        d.reference_values.r#type.as_mut()
    {
        let digests =
            Digests { digests: vec![RawDigest { sha2_384: actual, ..Default::default() }] };
        reference
            .root_layer
            .as_mut()
            .expect("no root layer reference values")
            .amd_sev
            .as_mut()
            .expect("no AMD SEV-SNP reference values")
            .stage0 = Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(digests)),
        });
    } else {
        panic!("invalid reference value type");
    }

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_fails_with_wrong_initial_measurement() {
    let mut d = AttestationData::load_milan_oc_legacy();

    let mut wrong = if let Some(EvidenceValues::OakContainers(values)) =
        verify_dice_chain_and_extract_evidence(&d.evidence)
            .expect("invalid DICE chain")
            .evidence_values
            .as_ref()
    {
        if let Some(Report::SevSnp(report)) =
            values.root_layer.as_ref().expect("no root layer").report.as_ref()
        {
            Some(report.initial_measurement.clone())
        } else {
            None
        }
    } else {
        None
    }
    .expect("invalid DICE evidence");
    wrong[0] ^= 1;

    if let Some(reference_values::Type::OakContainers(reference)) =
        d.reference_values.r#type.as_mut()
    {
        let digests =
            Digests { digests: vec![RawDigest { sha2_384: wrong, ..Default::default() }] };
        reference
            .root_layer
            .as_mut()
            .expect("no root layer reference values")
            .amd_sev
            .as_mut()
            .expect("no AMD SEV-SNP reference values")
            .stage0 = Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(digests)),
        });
    } else {
        panic!("invalid reference value type");
    }

    assert_failure(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_fails_with_empty_args() {
    let evidence = Evidence::default();
    let endorsements = Endorsements::default();
    let reference_values = ReferenceValues::default();

    assert_failure(verify(0, &evidence, &endorsements, &reference_values));
}

#[test]
fn verify_non_matching_command_line_reference_value_failure() {
    let d = AttestationData::load_milan_rk_legacy();

    let mut reference_values = create_rk_reference_values();
    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakRestrictedKernel(rfs)) => {
            rfs.kernel_layer.as_mut().unwrap().kernel_cmd_line_text = Some(TextReferenceValue {
                r#type: Some(text_reference_value::Type::Regex(Regex {
                    value: String::from("this will fail"),
                })),
            });
        }
        Some(_) => {}
        None => {}
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
#[cfg(not(feature = "regex"))]
fn verify_fails_with_matching_command_line_reference_value_regex_set_and_regex_disabled() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = create_rk_reference_values();

    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakRestrictedKernel(rfs)) => {
            rfs.kernel_layer.as_mut().unwrap().kernel_cmd_line_text = Some(TextReferenceValue {
                r#type: Some(text_reference_value::Type::Regex(Regex {
                    value: String::from("^console=[a-zA-Z0-9]+$"),
                })),
            });
        }
        Some(_) => {}
        None => {}
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
#[cfg(feature = "regex")]
fn verify_succeeds_with_matching_command_line_reference_value_regex_set_and_regex_enabled() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = create_rk_reference_values();

    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakRestrictedKernel(rfs)) => {
            rfs.kernel_layer.as_mut().unwrap().kernel_cmd_line_text = Some(TextReferenceValue {
                r#type: Some(text_reference_value::Type::Regex(Regex {
                    value: String::from("^console=[a-zA-Z0-9]+$"),
                })),
            });
        }
        Some(_) => {}
        None => {}
    };

    assert_success(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn verify_fails_with_command_line_reference_value_set_and_obsolete_evidence() {
    let evidence = create_rk_obsolete_evidence();
    let endorsements = AttestationData::load_milan_rk_legacy().endorsements;
    let reference_values = create_rk_reference_values();

    assert_failure(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values));
}

#[test]
fn verify_succeeds_with_skip_command_line_reference_value_set_and_obsolete_evidence() {
    let evidence = create_rk_obsolete_evidence();
    let endorsements = AttestationData::load_milan_rk_legacy().endorsements;
    let mut reference_values = create_rk_reference_values();

    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakRestrictedKernel(rfs)) => {
            rfs.kernel_layer.as_mut().unwrap().kernel_cmd_line_text = Some(TextReferenceValue {
                r#type: Some(text_reference_value::Type::Skip(SkipVerification {})),
            });
        }
        Some(_) => {}
        None => {}
    };

    assert_success(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn containers_invalid_boot_loader_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The boot loader version can never reach 256, since it is represented as a u8
    // in the attestation report.
    oc.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .boot_loader = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn containers_invalid_microcode_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The microcode version can never reach 256, since it is represented as a
    // u8 in the attestation report.
    oc.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .microcode = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn containers_invalid_tcb_snp_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The SNP version can never reach 256, since it is represented as a u8 in
    // the attestation report.
    oc.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .snp = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn containers_invalid_tcb_tee_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The TEE version can never reach 256, since it is represented as a u8 in
    // the attestation report.
    oc.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .tee = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_stage0_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .stage0
        .as_mut()
        .expect("no stage 0 measurement")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_384
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_acpi_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .acpi
        .as_mut()
        .expect("no acpi value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_init_ram_fs_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .init_ram_fs
        .as_mut()
        .expect("no init RAM fs value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_kernel_cmd_line_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .kernel_cmd_line_text
        .as_mut()
        .expect("no kernel command-line value")
        .r#type
        .as_mut()
        .expect("no text reference value")
    {
        text_reference_value::Type::StringLiterals(strings) => {
            strings.value.clear();
            strings.value.push("wrong".to_owned());
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_kernel_image_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .kernel
        .as_mut()
        .expect("no kernel value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        kernel_binary_reference_value::Type::Digests(digests) => {
            digests
                .image
                .as_mut()
                .expect("no kernel image")
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_kernel_setup_data_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .kernel
        .as_mut()
        .expect("no kernel value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        kernel_binary_reference_value::Type::Digests(digests) => {
            digests
                .setup_data
                .as_mut()
                .expect("no kernel setup data")
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_system_image_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .system_layer
        .as_mut()
        .expect("no system layer")
        .system_image
        .as_mut()
        .expect("no system image value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_container_bundle_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .container_layer
        .as_mut()
        .expect("no container layer")
        .binary
        .as_mut()
        .expect("no container bundle value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn containers_invalid_container_config_fails() {
    let d = AttestationData::load_milan_oc_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    match oc
        .container_layer
        .as_mut()
        .expect("no container layer")
        .configuration
        .as_mut()
        .expect("no container config value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn verify_rk_invalid_boot_loader_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The boot loader version can never reach 256, since it is represented as a u8
    // in the attestation report.
    rk.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .boot_loader = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn verify_rk_invalid_microcode_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The microcode version can never reach 256, since it is represented as a
    // u8 in the attestation report.
    rk.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .microcode = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn restricted_kernel_invalid_tcb_snp_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The SNP version can never reach 256, since it is represented as a u8 in
    // the attestation report.
    rk.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .snp = 256;
    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[allow(deprecated)]
#[test]
fn restricted_kernel_invalid_tcb_tee_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The TEE version can never reach 256, since it is represented as a u8 in
    // the attestation report.
    rk.root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .min_tcb_version
        .as_mut()
        .expect("no TCB version")
        .tee = 256;

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_stage0_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .root_layer
        .as_mut()
        .expect("no root layer")
        .amd_sev
        .as_mut()
        .expect("invalid TEE platform")
        .stage0
        .as_mut()
        .expect("no stage 0 measurement")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_384
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_acpi_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .acpi
        .as_mut()
        .expect("no acpi value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_init_ram_fs_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .init_ram_fs
        .as_mut()
        .expect("no init RAM fs value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_kernel_cmd_line_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .kernel_cmd_line_text
        .as_mut()
        .expect("no kernel command-line value")
        .r#type
        .as_mut()
        .expect("no text reference value")
    {
        text_reference_value::Type::StringLiterals(strings) => {
            strings.value.clear();
            strings.value.push("wrong".to_owned());
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_kernel_image_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .kernel
        .as_mut()
        .expect("no kernel value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        kernel_binary_reference_value::Type::Digests(digests) => {
            digests
                .image
                .as_mut()
                .expect("no kernel image")
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_kernel_setup_data_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .kernel_layer
        .as_mut()
        .expect("no kernel layer")
        .kernel
        .as_mut()
        .expect("no kernel value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        kernel_binary_reference_value::Type::Digests(digests) => {
            digests
                .setup_data
                .as_mut()
                .expect("no kernel setup data")
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_invalid_application_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    match rk
        .application_layer
        .as_mut()
        .expect("no application layer")
        .binary
        .as_mut()
        .expect("no application binary value")
        .r#type
        .as_mut()
        .expect("no binary reference value")
    {
        binary_reference_value::Type::Digests(digests) => {
            digests
                .digests
                .as_mut_slice()
                .first_mut()
                .expect("no digest")
                .sha2_256
                .as_mut_slice()[5] ^= 255;
        }
        _ => panic!("wrong reference value type."),
    };

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn restricted_kernel_application_config_fails() {
    let d = AttestationData::load_milan_rk_legacy();
    let mut reference_values = make_reference_values(&d.evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    rk.application_layer.as_mut().expect("no application layer").configuration.replace(
        BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![RawDigest { sha2_256: vec![1; 32], ..Default::default() }],
            })),
        },
    );

    assert_failure(verify(d.make_valid_millis(), &d.evidence, &d.endorsements, &reference_values));
}

#[test]
fn verify_milan_oc_success() {
    let d = AttestationData::load_oc();

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_genoa_oc_success() {
    let d = AttestationData::load_genoa_oc();

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}

#[test]
fn verify_turin_oc_success() {
    let d = AttestationData::load_turin_oc();

    assert_success(verify(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &d.reference_values,
    ));
}
