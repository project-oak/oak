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
    util::convert_pem_to_raw,
    verifier::{to_attestation_results, verify, verify_dice_chain},
};
use oak_attestation_verification_test_utils::{
    create_containers_reference_values, create_rk_reference_values, reference_values_from_evidence,
};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, binary_reference_value, extracted_evidence::EvidenceValues,
        kernel_binary_reference_value, reference_values, root_layer_data::Report,
        text_reference_value, ApplicationLayerEndorsements, BinaryReferenceValue,
        ContainerLayerEndorsements, Digests, EndorsementReferenceValue, Endorsements, Evidence,
        InsecureReferenceValues, KernelLayerEndorsements, OakContainersEndorsements,
        OakRestrictedKernelEndorsements, ReferenceValues, Regex, RootLayerEndorsements,
        RootLayerReferenceValues, SkipVerification, SystemLayerEndorsements, TcbVersion,
        TextReferenceValue, TransparentReleaseEndorsement,
    },
    RawDigest,
};
use prost::Message;

const ENDORSEMENT_PATH: &str = "testdata/endorsement.json";
const SIGNATURE_PATH: &str = "testdata/endorsement.json.sig";
const LOG_ENTRY_PATH: &str = "testdata/logentry.json";
const CONTAINERS_VCEK_MILAN_CERT_DER: &str = "testdata/oc_vcek_milan.der";
const RK_VCEK_MILAN_CERT_DER: &str = "testdata/rk_vcek_milan.der";
const ENDORSER_PUBLIC_KEY_PATH: &str = "testdata/oak-development.pem";
const REKOR_PUBLIC_KEY_PATH: &str = "testdata/rekor_public_key.pem";
const CONTAINERS_EVIDENCE_PATH: &str = "testdata/oc_evidence.binarypb";
const RK_EVIDENCE_PATH: &str = "testdata/rk_evidence.binarypb";
const RK_OBSOLETE_EVIDENCE_PATH: &str = "testdata/rk_evidence_20240312.binarypb";
const FAKE_EVIDENCE_PATH: &str = "testdata/fake_evidence.binarypb";

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

// Creates a valid AMD SEV-SNP evidence instance for Oak Containers.
fn create_containers_evidence() -> Evidence {
    let serialized = fs::read(CONTAINERS_EVIDENCE_PATH).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid AMD SEV-SNP evidence instance for a restricted kernel
// application.
fn create_rk_evidence() -> Evidence {
    let serialized = fs::read(RK_EVIDENCE_PATH).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid AMD SEV-SNP evidence instance for a restricted kernel
// application but with obsolete DICE data that is still used by some clients.
fn create_rk_obsolete_evidence() -> Evidence {
    let serialized = fs::read(RK_OBSOLETE_EVIDENCE_PATH).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid fake evidence instance.
fn create_fake_evidence() -> Evidence {
    let serialized = fs::read(FAKE_EVIDENCE_PATH).expect("could not read fake evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode fake evidence")
}

// Creates valid endorsements for an Oak Containers chain.
fn create_containers_endorsements() -> Endorsements {
    let endorsement = fs::read(ENDORSEMENT_PATH).expect("couldn't read endorsement");
    let signature = fs::read(SIGNATURE_PATH).expect("couldn't read signature");
    let log_entry = fs::read(LOG_ENTRY_PATH).expect("couldn't read log entry");
    let vcek_milan_cert = fs::read(CONTAINERS_VCEK_MILAN_CERT_DER).expect("couldn't read TEE cert");

    // Use this for all binaries.
    let tre = TransparentReleaseEndorsement {
        endorsement,
        subject: vec![],
        endorsement_signature: signature,
        rekor_log_entry: log_entry,
    };

    let root_layer =
        RootLayerEndorsements { tee_certificate: vcek_milan_cert, stage0: Some(tre.clone()) };
    #[allow(deprecated)]
    let kernel_layer = KernelLayerEndorsements {
        kernel: Some(tre.clone()),
        kernel_image: Some(tre.clone()),
        kernel_cmd_line: Some(tre.clone()),
        init_ram_fs: Some(tre.clone()),
        memory_map: Some(tre.clone()),
        acpi: Some(tre.clone()),
    };
    let system_layer = SystemLayerEndorsements { system_image: Some(tre.clone()) };
    let container_layer =
        ContainerLayerEndorsements { binary: Some(tre.clone()), configuration: Some(tre.clone()) };

    let ends = OakContainersEndorsements {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    Endorsements {
        r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(ends)),
    }
}

// Creates valid endorsements for a restricted kernel application.
fn create_rk_endorsements() -> Endorsements {
    let vcek_milan_cert = fs::read(RK_VCEK_MILAN_CERT_DER).expect("couldn't read TEE cert");

    let root_layer = RootLayerEndorsements { tee_certificate: vcek_milan_cert, stage0: None };
    #[allow(deprecated)]
    let kernel_layer = KernelLayerEndorsements {
        kernel: None,
        kernel_image: None,
        kernel_cmd_line: None,
        init_ram_fs: None,
        memory_map: None,
        acpi: None,
    };
    let application_layer = ApplicationLayerEndorsements { binary: None, configuration: None };

    let ends = OakRestrictedKernelEndorsements {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        application_layer: Some(application_layer),
    };
    Endorsements {
        r#type: Some(
            oak_proto_rust::oak::attestation::v1::endorsements::Type::OakRestrictedKernel(ends),
        ),
    }
}

#[test]
fn verify_containers_succeeds() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let reference_values = create_containers_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_containers_explicit_reference_values() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let reference_values = reference_values_from_evidence(extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_rk_succeeds() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let reference_values = create_rk_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_rk_explicit_reference_values() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let reference_values = reference_values_from_evidence(extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fake_evidence() {
    let evidence = create_fake_evidence();
    let endorsements = create_containers_endorsements();
    let mut reference_values = create_containers_reference_values();
    if let Some(reference_values::Type::OakContainers(reference)) = reference_values.r#type.as_mut()
    {
        reference.root_layer = Some(RootLayerReferenceValues {
            insecure: Some(InsecureReferenceValues {}),
            ..Default::default()
        });
    } else {
        panic!("invalid reference value type");
    }

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fake_evidence_explicit_reference_values() {
    let evidence = create_fake_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let reference_values = reference_values_from_evidence(extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

// See b/327069120: This test can go once we properly endorse stage0.
#[test]
fn verify_fails_with_stage0_reference_value_set() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();

    // Set the stage0 field to something.
    let mut reference_values = create_containers_reference_values();
    let endorser_public_key_pem =
        fs::read_to_string(ENDORSER_PUBLIC_KEY_PATH).expect("couldn't read endorser public key");
    let rekor_public_key_pem =
        fs::read_to_string(REKOR_PUBLIC_KEY_PATH).expect("couldn't read rekor public key");

    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");
    let erv = EndorsementReferenceValue { endorser_public_key, rekor_public_key };
    let brv = BinaryReferenceValue {
        r#type: Some(
            oak_proto_rust::oak::attestation::v1::binary_reference_value::Type::Endorsement(erv),
        ),
    };
    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakContainers(rfs)) => {
            rfs.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().stage0 = Some(brv);
        }
        Some(_) => {}
        None => {}
    };

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_manipulated_root_public_key() {
    let mut evidence = create_containers_evidence();
    evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
    let endorsements = create_containers_endorsements();
    let reference_values = create_containers_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_unsupported_tcb_version() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let mut reference_values = create_containers_reference_values();

    let tcb_version = TcbVersion { boot_loader: 0, tee: 0, snp: u32::MAX, microcode: 0 };
    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakContainers(rfs)) => {
            rfs.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().min_tcb_version =
                Some(tcb_version);
        }
        Some(_) => {}
        None => {}
    };

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_succeeds_with_right_initial_measurement() {
    let evidence = create_containers_evidence();
    let actual = if let Some(EvidenceValues::OakContainers(values)) =
        verify_dice_chain(&evidence).expect("invalid DICE chain").evidence_values.as_ref()
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

    let endorsements = create_containers_endorsements();
    let mut reference_values = create_containers_reference_values();
    if let Some(reference_values::Type::OakContainers(reference)) = reference_values.r#type.as_mut()
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
            r#type: Some(
                oak_proto_rust::oak::attestation::v1::binary_reference_value::Type::Digests(
                    digests,
                ),
            ),
        });
    } else {
        panic!("invalid reference value type");
    }

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fails_with_wrong_initial_measurement() {
    let evidence = create_containers_evidence();
    let mut wrong = if let Some(EvidenceValues::OakContainers(values)) =
        verify_dice_chain(&evidence).expect("invalid DICE chain").evidence_values.as_ref()
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

    let endorsements = create_containers_endorsements();
    let mut reference_values = create_containers_reference_values();
    if let Some(reference_values::Type::OakContainers(reference)) = reference_values.r#type.as_mut()
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
            r#type: Some(
                oak_proto_rust::oak::attestation::v1::binary_reference_value::Type::Digests(
                    digests,
                ),
            ),
        });
    } else {
        panic!("invalid reference value type");
    }

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_empty_args() {
    let evidence = Evidence::default();
    let endorsements = Endorsements::default();
    let reference_values = ReferenceValues::default();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_fails_with_non_matching_command_line_reference_value_set() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
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

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
#[cfg(not(feature = "regex"))]
fn verify_fails_with_matching_command_line_reference_value_regex_set_and_regex_disabled() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
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

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
#[cfg(feature = "regex")]
fn verify_succeeds_with_matching_command_line_reference_value_regex_set_and_regex_enabled() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
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

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fails_with_command_line_reference_value_set_and_obsolete_evidence() {
    let evidence = create_rk_obsolete_evidence();
    let endorsements = create_rk_endorsements();
    let reference_values = create_rk_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_err());
    assert!(p.status() == Status::GenericFailure);
}

#[test]
fn verify_succeeds_with_skip_command_line_reference_value_set_and_obsolete_evidence() {
    let evidence = create_rk_obsolete_evidence();
    let endorsements = create_rk_endorsements();
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

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn containers_invalid_boot_loader_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_microcode_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The microcode version can never reach 256, since it is represented as a u8 in
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
        .microcode = 256;
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_tcb_snp_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The SNP version can never reach 256, since it is represented as a u8 in the
    // attestation report.
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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_tcb_tee_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

    let oc = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("wrong reference value type"),
    };
    // The TEE version can never reach 256, since it is represented as a u8 in the
    // attestation report.
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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_stage0_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_acpi_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_init_ram_fs_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_kernel_cmd_line_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_kernel_image_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_kernel_setup_data_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_system_image_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_container_bundle_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn containers_invalid_container_config_fails() {
    let evidence = create_containers_evidence();
    let endorsements = create_containers_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_boot_loader_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_microcode_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The microcode version can never reach 256, since it is represented as a u8 in
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
        .microcode = 256;
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_tcb_snp_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The SNP version can never reach 256, since it is represented as a u8 in the
    // attestation report.
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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_tcb_tee_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

    let rk = match reference_values.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("wrong reference value type"),
    };
    // The TEE version can never reach 256, since it is represented as a u8 in the
    // attestation report.
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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_stage0_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_acpi_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_init_ram_fs_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_kernel_cmd_line_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_kernel_image_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_kernel_setup_data_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_invalid_application_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}

#[test]
fn restricted_kernel_application_config_fails() {
    let evidence = create_rk_evidence();
    let endorsements = create_rk_endorsements();
    let extracted_evidence = verify_dice_chain(&evidence).expect("invalid DICE evidence");
    let mut reference_values = reference_values_from_evidence(extracted_evidence);

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
    assert!(verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values).is_err());
}
