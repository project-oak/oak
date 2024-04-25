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
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, binary_reference_value, extracted_evidence::EvidenceValues,
        kernel_binary_reference_value, reference_values, root_layer_data::Report,
        text_reference_value, AmdSevReferenceValues, ApplicationLayerEndorsements,
        ApplicationLayerReferenceValues, BinaryReferenceValue, ContainerLayerEndorsements,
        ContainerLayerReferenceValues, Digests, EndorsementReferenceValue, Endorsements, Evidence,
        InsecureReferenceValues, KernelBinaryReferenceValue, KernelLayerEndorsements,
        KernelLayerReferenceValues, OakContainersEndorsements, OakContainersReferenceValues,
        OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
        Regex, RootLayerEndorsements, RootLayerReferenceValues, SkipVerification, StringLiterals,
        SystemLayerEndorsements, SystemLayerReferenceValues, TcbVersion, TextReferenceValue,
        TransparentReleaseEndorsement,
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

// Creates valid reference values for an Oak Containers chain.
fn create_containers_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };

    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: Some(TcbVersion { boot_loader: 0, tee: 0, snp: 0, microcode: 0 }),
        allow_debug: false,
        // See b/327069120: Do not skip over stage0.
        stage0: Some(skip.clone()),
    };

    let root_layer = RootLayerReferenceValues { amd_sev: Some(amd_sev), ..Default::default() };
    #[allow(deprecated)]
    let kernel_layer = KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
        }),
        kernel_setup_data: None,
        kernel_image: None,
        kernel_cmd_line: None,
        kernel_cmd_line_regex: None,
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![String::from(
                    "console=ttyS0 panic=-1 earlycon=uart,io,0x3F8 brd.rd_nr=1 brd.rd_size=3072000 brd.max_part=1 ip=10.0.2.15:::255.255.255.0::eth0:off net.ifnames=0 quiet",
                )],
            })),
        }),
        init_ram_fs: Some(skip.clone()),
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
fn create_rk_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };

    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: Some(TcbVersion { boot_loader: 0, tee: 0, snp: 0, microcode: 0 }),
        allow_debug: false,
        // See b/327069120: Do not skip over stage0.
        stage0: Some(skip.clone()),
    };

    let root_layer = RootLayerReferenceValues { amd_sev: Some(amd_sev), ..Default::default() };
    #[allow(deprecated)]
    let kernel_layer = KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
        }),
        kernel_setup_data: None,
        kernel_image: None,
        kernel_cmd_line: None,
        kernel_cmd_line_regex: None,
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
