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

//! Tests for legacy attestation verification.

use std::fs;

use oak_attestation_verification::{
    get_expected_values,
    verifier::{
        to_attestation_results, verify, verify_dice_chain_and_extract_evidence,
        verify_with_expected_values,
    },
};
use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    RawDigest,
    attestation::v1::{
        BinaryReferenceValue, Digests, Endorsements, Evidence, ExpectedValues, ExtractedEvidence,
        ReferenceValues, Regex, TcbVersion, TcbVersionReferenceValue, TeePlatform,
        TextReferenceValue, attestation_results::Status, binary_reference_value,
        extracted_evidence::EvidenceValues, reference_values, root_layer_data::Report,
        tcb_version_reference_value, text_reference_value,
    },
};
use oak_sev_snp_attestation_report::{AmdProduct, AttestationReport};
use prost::Message;
use test_util::{
    attestation_data::AttestationData,
    create_reference_values_for_extracted_evidence, create_rk_reference_values,
    manipulate::{
        get_acpi_rv, get_init_ram_fs_rv, get_kernel_cmd_line_rv, get_kernel_rv, get_oc_config_rv,
        get_oc_container_rv, get_oc_system_image_rv, get_rk_application_rv, get_rk_config_rv,
        get_stage0_rv, manipulate_kernel_cmd_line, manipulate_kernel_image,
        manipulate_kernel_setup_data, manipulate_sha2_256, manipulate_sha2_384,
    },
};
use zerocopy::FromBytes;

const FAKE_EXPECTED_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/fake_expected_values.binarypb";

fn create_fake_expected_values() -> ExpectedValues {
    let serialized = fs::read(data_path(FAKE_EXPECTED_VALUES_PATH))
        .expect("could not read fake expected values");
    ExpectedValues::decode(serialized.as_slice()).expect("could not decode fake expected values")
}

// Shorthand that produces digest-based reference values from evidence.
fn make_reference_values(evidence: &Evidence) -> ReferenceValues {
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(evidence).expect("invalid DICE evidence");
    create_reference_values_for_extracted_evidence(extracted_evidence)
}

fn get_amd_product(d: &AttestationData) -> Option<AmdProduct> {
    let root_layer = d.evidence.root_layer.as_ref().unwrap();
    match root_layer.platform() {
        TeePlatform::Unspecified => None,
        TeePlatform::AmdSevSnp | TeePlatform::None => {
            let report =
                AttestationReport::ref_from_bytes(&root_layer.remote_attestation_report).unwrap();
            Some(report.data.get_product())
        }
        TeePlatform::IntelTdx => None,
    }
}

// Helper which asserts success of the legacy verify() call.
fn assert_success(result: anyhow::Result<ExtractedEvidence>) {
    let proto = to_attestation_results(&result);

    if proto.status() != Status::Success {
        eprintln!("======================================");
        eprintln!("code={} reason={}", proto.status, proto.reason);
        eprintln!("======================================");
    }
    assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
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
    assert!(result.is_err(), "Expected failure but got success: {:?}", result);
    assert!(proto.status() == Status::GenericFailure);
}

macro_rules! test_verify_success {
    ($($name:tt)*) => {
        mod test_verify_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();

                    assert_success(verify(
                        d.make_valid_millis(),
                        &d.evidence,
                        &d.endorsements,
                        &d.reference_values,
                    ));
                }
            )*
        }
    }
}

test_verify_success! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_cb
    load_fake
}

macro_rules! test_verify_explicit_reference_values_success {
    ($($name:tt)*) => {
        mod test_verify_explicit_reference_values_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let d = AttestationData::$name();
                    let reference_values = make_reference_values(&d.evidence);

                    assert_success(verify(
                        d.make_valid_millis(),
                        &d.evidence,
                        &d.endorsements,
                        &reference_values,
                    ));
                }
            )*
        }
    }
}

test_verify_explicit_reference_values_success! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_fake
}

#[test]
fn verify_fake_evidence_split_verify_calls() {
    let d = AttestationData::load_fake();
    let reference_values = make_reference_values(&d.evidence);
    let computed_expected_values =
        get_expected_values(d.make_valid_millis(), &d.endorsements, &reference_values).unwrap();

    assert_success(verify_with_expected_values(
        d.make_valid_millis(),
        &d.evidence,
        &d.endorsements,
        &computed_expected_values,
    ));
}

#[test]
fn verify_fake_evidence_explicit_reference_values_expected_values_correct() {
    let d = AttestationData::load_fake();
    let reference_values = make_reference_values(&d.evidence);
    let computed_expected_values =
        get_expected_values(d.make_valid_millis(), &d.endorsements, &reference_values).unwrap();

    let mut buf = vec![];
    computed_expected_values
        .encode(&mut buf)
        .expect("Could not encode expected values from result");

    assert_eq!(computed_expected_values, create_fake_expected_values());
}

macro_rules! verify_manipulated_root_public_key_failure {
    ($($name:tt)*) => {
        mod verify_manipulated_root_public_key_failure {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();

                    d.evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;

                    assert_failure(verify(
                        d.make_valid_millis(),
                        &d.evidence,
                        &d.endorsements,
                        &d.reference_values,
                    ));
                }
            )*
        }
    }
}

verify_manipulated_root_public_key_failure! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_cb
    load_fake
}

macro_rules! verify_unsupported_tcb_version_failure {
    ($($name:tt)*) => {
        #[allow(deprecated)]
        mod verify_unsupported_tcb_version_failure {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();

                    let tcb_version = TcbVersion { boot_loader: 0, tee: 0, snp: u32::MAX, microcode: 0, fmc: 0 };
                    match d.reference_values.r#type.as_mut() {
                        Some(reference_values::Type::OakContainers(rfs)) => {
                            rfs.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().min_tcb_version =
                                Some(tcb_version);
                        }
                        Some(reference_values::Type::OakRestrictedKernel(rfs)) => {
                            rfs.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().min_tcb_version =
                                Some(tcb_version);
                        }
                        Some(reference_values::Type::Cb(rfs)) => {
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
            )*
        }
    }
}

verify_unsupported_tcb_version_failure! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_cb
}

// Remove TCB version reference value for all non-encountered CPU models.
macro_rules! verify_unpopulated_tcb_version_success {
    ($($name:tt)*) => {
        #[allow(deprecated)]
        mod verify_unpopulated_tcb_version_success {
            use super::*;

            $(
                #[test]
                fn $name() {
                    let mut d = AttestationData::$name();
                    let amd_product = get_amd_product(&d);

                    match d.reference_values.r#type.as_mut() {
                        Some(reference_values::Type::OakContainers(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => {
                                    amd_sev.genoa = None;
                                    amd_sev.turin = None;
                                }
                                Some(AmdProduct::Genoa) => {
                                    amd_sev.milan = None;
                                    amd_sev.turin = None;
                                }
                                Some(AmdProduct::Turin) => {
                                    amd_sev.milan = None;
                                    amd_sev.genoa = None;
                                }
                                Some(AmdProduct::Unsupported) => {
                                    amd_sev.milan = None;
                                    amd_sev.genoa = None;
                                    amd_sev.turin = None;
                                }
                                None => panic!("missing AMD product"),
                            }
                        }
                        Some(reference_values::Type::OakRestrictedKernel(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => {
                                    amd_sev.genoa = None;
                                    amd_sev.turin = None;
                                }
                                Some(AmdProduct::Genoa) => {
                                    amd_sev.milan = None;
                                    amd_sev.turin = None;
                                }
                                Some(AmdProduct::Turin) => {
                                    amd_sev.milan = None;
                                    amd_sev.genoa = None;
                                }
                                Some(AmdProduct::Unsupported) => {
                                    amd_sev.milan = None;
                                    amd_sev.genoa = None;
                                    amd_sev.turin = None;
                                }
                                None => panic!("missing AMD product"),
                            }
                        }
                        Some(reference_values::Type::Cb(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => {
                                    amd_sev.genoa = None;
                                    amd_sev.turin = None;
                                }
                                Some(AmdProduct::Genoa) => {
                                    amd_sev.milan = None;
                                    amd_sev.turin = None;
                                }
                                Some(AmdProduct::Turin) => {
                                    amd_sev.milan = None;
                                    amd_sev.genoa = None;
                                }
                                Some(AmdProduct::Unsupported) => {
                                    amd_sev.milan = None;
                                    amd_sev.genoa = None;
                                    amd_sev.turin = None;
                                }
                                None => panic!("missing AMD product"),
                            }
                        }
                        _ => panic!("malformed reference values"),
                    }

                    assert_success(verify(
                        d.make_valid_millis(),
                        &d.evidence,
                        &d.endorsements,
                        &d.reference_values,
                    ));
                }
            )*
        }
    }
}

verify_unpopulated_tcb_version_success! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_cb
    load_fake
}

// Remove TCB version reference value for the encountered CPU model.
macro_rules! verify_unpopulated_tcb_version_failure {
    ($($load_name:tt)*) => {
        #[allow(deprecated)]
        mod verify_unpopulated_tcb_version_failure {
            use super::*;

            $(
                #[test]
                fn $load_name() {
                    let mut d = AttestationData::$load_name();
                    let amd_product = get_amd_product(&d);

                    match d.reference_values.r#type.as_mut() {
                        Some(reference_values::Type::OakContainers(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => {
                                    amd_sev.milan = None;
                                }
                                Some(AmdProduct::Genoa) => {
                                    amd_sev.genoa = None;
                                }
                                Some(AmdProduct::Turin) => {
                                    amd_sev.turin = None;
                                }
                                _ => {panic!("unexpected AMD product")}
                            }
                        }
                        Some(reference_values::Type::OakRestrictedKernel(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => {
                                    amd_sev.milan = None;
                                }
                                Some(AmdProduct::Genoa) => {
                                    amd_sev.genoa = None;
                                }
                                Some(AmdProduct::Turin) => {
                                    amd_sev.turin = None;
                                }
                                _ => panic!("unexpected AMD product"),
                            }
                        }
                        Some(reference_values::Type::Cb(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => {
                                    amd_sev.milan = None;
                                }
                                Some(AmdProduct::Genoa) => {
                                    amd_sev.genoa = None;
                                }
                                Some(AmdProduct::Turin) => {
                                    amd_sev.turin = None;
                                }
                                _ => panic!("unexpected AMD product"),
                            }
                        }
                        _ => panic!("malformed reference values"),
                    }

                    assert_failure(verify(
                        d.make_valid_millis(),
                        &d.evidence,
                        &d.endorsements,
                        &d.reference_values,
                    ));
                }
            )*
        }
    }
}

verify_unpopulated_tcb_version_failure! {
    load_milan_oc_release
    load_milan_oc_staging
    load_milan_rk_release
    load_milan_rk_staging
    load_genoa_oc
    load_turin_oc
    load_cb
}

fn manipulate_boot_loader(rv: &mut Option<TcbVersionReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(tcb_version_reference_value::Type::Minimum(m)) = &mut stripped.r#type {
            m.boot_loader = 256;
        }
    }
}

fn manipulate_microcode(rv: &mut Option<TcbVersionReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(tcb_version_reference_value::Type::Minimum(m)) = &mut stripped.r#type {
            m.microcode = 256;
        }
    }
}

fn manipulate_tee(rv: &mut Option<TcbVersionReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(tcb_version_reference_value::Type::Minimum(m)) = &mut stripped.r#type {
            m.tee = 256;
        }
    }
}

fn manipulate_snp(rv: &mut Option<TcbVersionReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(tcb_version_reference_value::Type::Minimum(m)) = &mut stripped.r#type {
            m.snp = 256;
        }
    }
}

fn manipulate_fmc(rv: &mut Option<TcbVersionReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(tcb_version_reference_value::Type::Minimum(m)) = &mut stripped.r#type {
            m.fmc = 256;
        }
    }
}

// $manip_fn sets various TCB version fields to 256 which is an invalid value.
// All such values are represented as u8 in the attestation report, so it can
// never be attained.
macro_rules! verify_tcb_version_failure_tests {
    ($module_name:tt, $manip_fn:tt, $($load_name:tt, )*) => {
        #[allow(deprecated)]
        mod $module_name {
            use super::*;

            $(
                #[test]
                fn $load_name() {
                    let mut d = AttestationData::$load_name();
                    let amd_product = get_amd_product(&d);

                    match d.reference_values.r#type.as_mut() {
                        Some(reference_values::Type::OakContainers(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => $manip_fn(&mut amd_sev.milan),
                                Some(AmdProduct::Genoa) => $manip_fn(&mut amd_sev.genoa),
                                Some(AmdProduct::Turin) => $manip_fn(&mut amd_sev.turin),
                                _ => panic!("unexpected AMD product"),
                            }
                        }
                        Some(reference_values::Type::OakRestrictedKernel(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => $manip_fn(&mut amd_sev.milan),
                                Some(AmdProduct::Genoa) => $manip_fn(&mut amd_sev.genoa),
                                Some(AmdProduct::Turin) => $manip_fn(&mut amd_sev.turin),
                                _ => panic!("unexpected AMD product"),
                            }
                        }
                        Some(reference_values::Type::Cb(r)) => {
                            let amd_sev = r.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap();
                            amd_sev.min_tcb_version = None;
                            match amd_product {
                                Some(AmdProduct::Milan) => $manip_fn(&mut amd_sev.milan),
                                Some(AmdProduct::Genoa) => $manip_fn(&mut amd_sev.genoa),
                                Some(AmdProduct::Turin) => $manip_fn(&mut amd_sev.turin),
                                _ => panic!("unexpected AMD product"),
                            }
                        }
                        _ => panic!("malformed reference values"),
                    }

                    assert_failure(verify(
                        d.make_valid_millis(),
                        &d.evidence,
                        &d.endorsements,
                        &d.reference_values,
                    ));
                }
            )*
        }
    }
}

verify_tcb_version_failure_tests! {
    verify_invalid_tcb_version_boot_loader_failure, manipulate_boot_loader,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
    load_cb,
}

verify_tcb_version_failure_tests! {
    verify_invalid_tcb_version_microcode_failure, manipulate_microcode,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
    load_cb,
}

verify_tcb_version_failure_tests! {
    verify_invalid_tcb_version_tee_failure, manipulate_tee,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
    load_cb,
}

verify_tcb_version_failure_tests! {
    verify_invalid_tcb_version_snp_failure, manipulate_snp,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
    load_cb,
}

verify_tcb_version_failure_tests! {
    verify_invalid_tcb_version_fmc_failure, manipulate_fmc,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
    load_cb,
}

#[test]
fn verify_succeeds_with_right_initial_measurement() {
    let mut d = AttestationData::load_milan_oc_staging();

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
    let mut d = AttestationData::load_milan_oc_staging();

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
#[cfg(not(feature = "regex"))]
fn verify_fails_with_matching_command_line_reference_value_regex_set_and_regex_disabled() {
    let d = AttestationData::load_milan_rk_staging();
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
    let d = AttestationData::load_milan_rk_staging();
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

#[allow(deprecated)]
#[test]
fn containers_invalid_boot_loader_fails() {
    let d = AttestationData::load_milan_oc_staging();
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
    let d = AttestationData::load_milan_oc_staging();
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
    let d = AttestationData::load_milan_oc_staging();
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
    let d = AttestationData::load_milan_oc_staging();
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

#[allow(deprecated)]
#[test]
fn verify_rk_invalid_boot_loader_fails() {
    let d = AttestationData::load_milan_rk_staging();
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
    let d = AttestationData::load_milan_rk_staging();
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
    let d = AttestationData::load_milan_rk_staging();
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
    let d = AttestationData::load_milan_rk_staging();
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

// Macro that creates many tests that observe failure after manipulating
// reference values of a working attestation sample.
macro_rules! manipulate_tests {
    ($module_name:tt, $get_fn:tt, $manip_fn:tt, $($load_name:tt, )*) => {
        mod $module_name {
            use super::*;

            $(
                #[test]
                fn $load_name() {
                    let d = AttestationData::$load_name();
                    let mut rvs = make_reference_values(&d.evidence);
                    let rv = $get_fn(&mut rvs);
                    $manip_fn(rv);

                    assert_failure(verify(
                        d.make_valid_millis(),
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
    get_stage0_rv, manipulate_sha2_384,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_init_ram_fs_manipulate_digests_failure,
    get_init_ram_fs_rv, manipulate_sha2_256,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_acpi_manipulate_digests_failure,
    get_acpi_rv, manipulate_sha2_256,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_kernel_image_manipulate_digests_failure,
    get_kernel_rv, manipulate_kernel_image,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_kernel_setup_data_manipulate_digests_failure,
    get_kernel_rv, manipulate_kernel_setup_data,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_kernel_cmd_line_manipulate_value_failure,
    get_kernel_cmd_line_rv, manipulate_kernel_cmd_line,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_milan_rk_release,
    load_milan_rk_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_oc_system_image_manipulate_digests_failure,
    get_oc_system_image_rv, manipulate_sha2_256,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_oc_container_manipulate_digests_failure,
    get_oc_container_rv, manipulate_sha2_256,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_oc_config_manipulate_digests_failure,
    get_oc_config_rv, manipulate_sha2_256,
    load_milan_oc_release,
    load_milan_oc_staging,
    load_genoa_oc,
    load_turin_oc,
}

manipulate_tests! {
    amd_rk_application_manipulate_digests_failure,
    get_rk_application_rv, manipulate_sha2_256,
    load_milan_rk_release,
    load_milan_rk_staging,
}

manipulate_tests! {
    amd_rk_config_manipulate_digests_failure,
    get_rk_config_rv, manipulate_sha2_256,
    load_milan_rk_release,
    load_milan_rk_staging,
}
