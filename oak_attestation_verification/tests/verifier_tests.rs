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
    convert_pem_to_raw,
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
        text_reference_value, AmdSevReferenceValues, ApplicationLayerEndorsements,
        ApplicationLayerReferenceValues, BinaryReferenceValue, ClaimReferenceValue,
        ContainerLayerEndorsements, ContainerLayerReferenceValues, Digests,
        EndorsementReferenceValue, Endorsements, Evidence, ExpectedValues, InsecureReferenceValues,
        KernelBinaryReferenceValue, KernelLayerEndorsements, KernelLayerReferenceValues, KeyType,
        OakContainersEndorsements, OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues, Regex, RootLayerEndorsements,
        RootLayerReferenceValues, SkipVerification, StringLiterals, SystemLayerEndorsements,
        SystemLayerReferenceValues, TcbVersion, TextReferenceValue, TransparentReleaseEndorsement,
        VerifyingKey, VerifyingKeyReferenceValue, VerifyingKeySet,
    },
    RawDigest,
};
use prost::Message;

// Transparent Release endorsement
const ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/endorsement.json";
const SIGNATURE_PATH: &str = "oak_attestation_verification/testdata/endorsement.json.sig";
const LOG_ENTRY_PATH: &str = "oak_attestation_verification/testdata/logentry.json";
const ENDORSER_PUBLIC_KEY_PATH: &str =
    "oak_attestation_verification/testdata/endorser_public_key.pem";
const REKOR_PUBLIC_KEY_PATH: &str = "oak_attestation_verification/testdata/rekor_public_key.pem";

// Certificates
const OC_VCEK_MILAN_CERT_DER: &str = "oak_attestation_verification/testdata/oc_vcek_milan.der";
const GENOA_VCEK_CERT_DER: &str = "oak_attestation_verification/testdata/vcek_genoa.der";
const RK_VCEK_MILAN_CERT_DER: &str = "oak_attestation_verification/testdata/rk_vcek_milan.der";

// CB attestation
const CB_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/cb_evidence.binarypb";
const CB_ENDORSEMENT_PATH: &str = "oak_attestation_verification/testdata/cb_endorsements.binarypb";
const CB_REFERENCE_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/cb_reference_values.binarypb";

// Fake attestation
const FAKE_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/fake_evidence.binarypb";
const FAKE_EXPECTED_VALUES_PATH: &str =
    "oak_attestation_verification/testdata/fake_expected_values.binarypb";

// AMD Genoa attestation with Oak Containers
const GENOA_OC_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_evidence.binarypb";
const GENOA_OC_REFERENCE_PATH: &str =
    "oak_attestation_verification/testdata/genoa_oc_reference_values.binarypb";

// Legacy Oak Containers attestation
const OC_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/oc_evidence.binarypb";

// Legacy Restricted Kernel attestation
const RK_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/rk_evidence.binarypb";
const RK_OBSOLETE_EVIDENCE_PATH: &str =
    "oak_attestation_verification/testdata/rk_evidence_20240312.binarypb";

// Pretend the tests run at this time: 1 March 2024, 12:00 UTC. This date must
// be valid with respect to the endorsement behind ENDORSEMENT_PATH.
const NOW_UTC_MILLIS: i64 = 1709294400000;

// Creates a valid AMD SEV-SNP evidence instance for a CB setup.
fn create_cb_evidence() -> Evidence {
    let serialized = fs::read(data_path(CB_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid AMD SEV-SNP endorsement instance for a CB setup.
fn create_cb_endorsements() -> Endorsements {
    let serialized = fs::read(data_path(CB_ENDORSEMENT_PATH)).expect("could not read endorsement");
    Endorsements::decode(serialized.as_slice()).expect("could not decode endorsement")
}

// Creates valid AMD SEV-SNP reference values instance for a CB setup.
fn create_cb_reference_values() -> ReferenceValues {
    let serialized =
        fs::read(data_path(CB_REFERENCE_VALUES_PATH)).expect("could not read references");
    ReferenceValues::decode(serialized.as_slice()).expect("could not decode references")
}

// Creates a valid AMD SEV-SNP evidence instance for Oak Containers.
fn create_oc_evidence() -> Evidence {
    let serialized = fs::read(data_path(OC_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Creates a valid AMD SEV-SNP evidence instance for a restricted kernel
// application.
fn create_rk_evidence() -> Evidence {
    let serialized = fs::read(data_path(RK_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

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

// Creates an endorsement for the instance in test data which happens to be
// a stage1 endorsement.
fn create_stage1_endorsement() -> TransparentReleaseEndorsement {
    let endorsement = fs::read(data_path(ENDORSEMENT_PATH)).expect("couldn't read endorsement");
    let endorsement_signature =
        fs::read(data_path(SIGNATURE_PATH)).expect("couldn't read signature");
    let rekor_log_entry = fs::read(data_path(LOG_ENTRY_PATH)).expect("couldn't read log entry");

    TransparentReleaseEndorsement {
        endorsement,
        subject: vec![],
        endorsement_signature,
        rekor_log_entry,
    }
}

// Creates mock endorsements for an Oak Containers chain.
fn create_oc_endorsements() -> Endorsements {
    let vcek_milan_cert =
        fs::read(data_path(OC_VCEK_MILAN_CERT_DER)).expect("couldn't read TEE cert");
    let root_layer = RootLayerEndorsements { tee_certificate: vcek_milan_cert, stage0: None };
    let kernel_layer = KernelLayerEndorsements {
        kernel: None,
        kernel_cmd_line: None,
        init_ram_fs: Some(create_stage1_endorsement()),
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

// Creates mock endorsements instance for a restricted kernel application.
fn create_rk_endorsements() -> Endorsements {
    let vcek_milan_cert =
        fs::read(data_path(RK_VCEK_MILAN_CERT_DER)).expect("couldn't read TEE cert");
    let root_layer = RootLayerEndorsements { tee_certificate: vcek_milan_cert, stage0: None };
    let kernel_layer = KernelLayerEndorsements {
        kernel: None,
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
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
    }
}

// Creates a valid AMD SEV-SNP evidence instance for Oak Containers running in
// Genoa CPU.
fn create_genoa_oc_evidence() -> Evidence {
    let serialized = fs::read(data_path(GENOA_OC_EVIDENCE_PATH)).expect("could not read evidence");
    Evidence::decode(serialized.as_slice()).expect("could not decode evidence")
}

// Create a valid endorsement for Oak container.
fn create_genoa_oc_endorsements() -> Endorsements {
    let vcek_milan_cert =
        fs::read(data_path(GENOA_VCEK_CERT_DER)).expect("could not read TEE cert");
    let root_layer = oak_proto_rust::oak::attestation::v1::RootLayerEndorsements {
        tee_certificate: vcek_milan_cert,
        stage0: None,
    };
    let ends = oak_proto_rust::oak::attestation::v1::OakContainersEndorsements {
        root_layer: Some(root_layer),
        container_layer: None,
        kernel_layer: None,
        system_layer: None,
    };
    oak_proto_rust::oak::attestation::v1::Endorsements {
        r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(ends)),
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
    }
}

fn create_genoa_oc_reference_values() -> ReferenceValues {
    let serialized =
        fs::read(data_path(GENOA_OC_REFERENCE_PATH)).expect("could not read reference");
    ReferenceValues::decode(serialized.as_slice()).expect("could not decode reference")
}

// Creates a good public-key based BinaryReferenceValue to verify the
// endorsement behind `oak_attestation_verification/testdata:endorsement`.
// This happens to be stage1 for no reason. The subject name there is
// incorrect but this is irrelevant for the test.
//
// TODO: b/379268663 - Stop populating the old-style fields endorser_public_key
//                     and rekor_public_key.
fn create_stage1_reference_value() -> BinaryReferenceValue {
    let endorser_public_key_pem = fs::read_to_string(data_path(ENDORSER_PUBLIC_KEY_PATH))
        .expect("couldn't read endorser public key");
    let rekor_public_key_pem = fs::read_to_string(data_path(REKOR_PUBLIC_KEY_PATH))
        .expect("couldn't read Rekor public key");
    let endorser_public_key = convert_pem_to_raw(endorser_public_key_pem.as_str())
        .expect("failed to convert endorser key");
    let rekor_public_key =
        convert_pem_to_raw(&rekor_public_key_pem).expect("failed to convert Rekor key");

    let endorser_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: 1, // Unused since this is legacy attestation verification.
        raw: endorser_public_key.clone(),
    };
    let rekor_key = VerifyingKey {
        r#type: KeyType::EcdsaP256Sha256.into(),
        key_id: 0, // Unused
        raw: rekor_public_key.clone(),
    };

    let claim_types = vec![
        "https://project-oak.github.io/oak/test_claim_1".to_owned(),
        "https://project-oak.github.io/oak/test_claim_2".to_owned(),
    ];

    BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Endorsement(EndorsementReferenceValue {
            endorser: Some(VerifyingKeySet { keys: [endorser_key].to_vec(), ..Default::default() }),
            required_claims: Some(ClaimReferenceValue { claim_types }),
            rekor: Some(VerifyingKeyReferenceValue {
                r#type: Some(oak_proto_rust::oak::attestation::v1::verifying_key_reference_value::Type::Verify(
                    VerifyingKeySet { keys: [rekor_key].to_vec(), ..Default::default() },
                ))
            }),
            ..Default::default()
        })),
    }
}

// Creates valid reference values for an Oak Containers chain.
// All endorsements are skipped with the exception of the one which happens
// to be available under testdata.
fn create_oc_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };

    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: Some(TcbVersion { boot_loader: 3, tee: 0, snp: 20, microcode: 209 }),
        allow_debug: false,
        stage0: Some(skip.clone()),
    };

    let root_layer = RootLayerReferenceValues { amd_sev: Some(amd_sev), ..Default::default() };
    let kernel_layer = KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![String::from(
                    "console=ttyS0 panic=-1 earlycon=uart,io,0x3F8 brd.rd_nr=1 brd.rd_size=3072000 brd.max_part=1 ip=10.0.2.15:::255.255.255.0::eth0:off net.ifnames=0 quiet",
                )],
            })),
        }),
        // Insert the stage1 reference value where it belongs.
        init_ram_fs: Some(create_stage1_reference_value()),
        memory_map: Some(skip.clone()),
        acpi: Some(skip.clone()),
    };
    let system_layer = SystemLayerReferenceValues { system_image: Some(skip.clone()) };
    let container_layer = ContainerLayerReferenceValues {
        binary: Some(skip.clone()),
        configuration: Some(skip.clone()),
    };
    let vs = OakContainersReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    ReferenceValues { r#type: Some(reference_values::Type::OakContainers(vs)) }
}

// Creates valid reference values for a restricted kernel application.
// Skips verification of endorsements whenever they are by public key.
fn create_rk_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };

    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: Some(TcbVersion { boot_loader: 3, tee: 0, snp: 20, microcode: 209 }),
        allow_debug: false,
        stage0: Some(skip.clone()),
    };

    let root_layer = RootLayerReferenceValues { amd_sev: Some(amd_sev), ..Default::default() };
    #[allow(deprecated)]
    let kernel_layer = KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![String::from("console=ttyS0")],
            })),
        }),
        init_ram_fs: Some(skip.clone()),
        memory_map: Some(skip.clone()),
        acpi: Some(skip.clone()),
    };
    let application_layer = ApplicationLayerReferenceValues {
        binary: Some(skip.clone()),
        configuration: Some(skip.clone()),
    };
    let vs = OakRestrictedKernelReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        application_layer: Some(application_layer),
    };
    ReferenceValues { r#type: Some(reference_values::Type::OakRestrictedKernel(vs)) }
}

#[test]
fn verify_containers_succeeds() {
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let reference_values = create_oc_reference_values();

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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
fn verify_cb_succeeds() {
    let evidence = create_cb_evidence();
    let endorsements = create_cb_endorsements();
    let reference_values = create_cb_reference_values();

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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let endorsements = create_oc_endorsements();
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
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
fn verify_fake_evidence_split_verify_calls() {
    let evidence = create_fake_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
    let reference_values = reference_values_from_evidence(extracted_evidence);

    let computed_expected_values =
        get_expected_values(NOW_UTC_MILLIS, &endorsements, &reference_values).unwrap();

    let r = verify_with_expected_values(
        NOW_UTC_MILLIS,
        &evidence,
        &endorsements,
        &computed_expected_values,
    );

    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn verify_fake_evidence_explicit_reference_values_expected_values_correct() {
    let evidence = create_fake_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
    let reference_values = reference_values_from_evidence(extracted_evidence);

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
    let mut evidence = create_oc_evidence();
    evidence.root_layer.as_mut().unwrap().eca_public_key[0] += 1;
    let endorsements = create_oc_endorsements();
    let reference_values = create_oc_reference_values();

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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let mut reference_values = create_oc_reference_values();

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
    let evidence = create_oc_evidence();
    let actual = if let Some(EvidenceValues::OakContainers(values)) =
        verify_dice_chain_and_extract_evidence(&evidence)
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

    let endorsements = create_oc_endorsements();
    let mut reference_values = create_oc_reference_values();
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
    let evidence = create_oc_evidence();
    let mut wrong = if let Some(EvidenceValues::OakContainers(values)) =
        verify_dice_chain_and_extract_evidence(&evidence)
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

    let endorsements = create_oc_endorsements();
    let mut reference_values = create_oc_reference_values();
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let evidence = create_oc_evidence();
    let endorsements = create_oc_endorsements();
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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
    let extracted_evidence =
        verify_dice_chain_and_extract_evidence(&evidence).expect("invalid DICE evidence");
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

#[test]
fn verify_genoa() {
    let evidence = create_genoa_oc_evidence();
    let endorsements = create_genoa_oc_endorsements();
    let reference_values = create_genoa_oc_reference_values();

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}
