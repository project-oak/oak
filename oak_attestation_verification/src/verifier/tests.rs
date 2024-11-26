// Creates a signed endorsement for a digest.
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
//
// Tests attestation verification once with most endorsements populated
// and reference values verified via public keys, where the underlying
// endorsements are created and signed on the fly. For other tests (in
// particular negative ones) see verifier_tests.rs.

use std::fs;

use oak_file_utils::data_path;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, extracted_evidence::EvidenceValues, kernel_binary_reference_value,
        reference_values, text_reference_value, AmdSevReferenceValues,
        ApplicationLayerEndorsements, ApplicationLayerReferenceValues, BinaryReferenceValue,
        ContainerLayerEndorsements, ContainerLayerReferenceValues, Endorsements, Evidence,
        ExtractedEvidence, KernelBinaryReferenceValue, KernelLayerEndorsements,
        KernelLayerReferenceValues, OakContainersEndorsements, OakContainersReferenceValues,
        OakRestrictedKernelEndorsements, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerEndorsements, RootLayerReferenceValues, SkipVerification, StringLiterals,
        SystemLayerEndorsements, SystemLayerReferenceValues, TcbVersion, TextReferenceValue,
        TransparentReleaseEndorsement,
    },
    RawDigest,
};
use prost::Message;

use crate::{
    extract::extract_evidence,
    test_util::{
        binary_reference_value_for_endorser_pk, fake_endorsement, new_random_signing_keypair,
        serialize_and_sign_endorsement,
    },
    verifier::{to_attestation_results, verify, Status},
};

const OC_VCEK_MILAN_CERT_DER: &str = "oak_attestation_verification/testdata/oc_vcek_milan.der";
const RK_VCEK_MILAN_CERT_DER: &str = "oak_attestation_verification/testdata/rk_vcek_milan.der";
const OC_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/oc_evidence.binarypb";
const RK_EVIDENCE_PATH: &str = "oak_attestation_verification/testdata/rk_evidence.binarypb";

// Pretend the tests run at this time: 1 Nov 2024, 12:00 UTC. This date
// must be valid with respect to the period hardwired in
// test_util::fake_endorsement().
const NOW_UTC_MILLIS: i64 = 1730462400000;

#[test]
fn test_oc_success() {
    let evidence = create_oc_evidence();
    let extracted_evidence = extract_evidence(&evidence).expect("failed to extract evidence");
    let (endorsements, reference_values) =
        create_oc_endorsements_reference_values(&extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn test_rk_success() {
    let evidence = create_rk_evidence();
    let extracted_evidence = extract_evidence(&evidence).expect("failed to extract evidence");
    let (endorsements, reference_values) =
        create_rk_endorsements_reference_values(&extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
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

fn create_endorsement(
    digest: &RawDigest,
    claim_types: Vec<&str>,
) -> (TransparentReleaseEndorsement, p256::PublicKey) {
    let (signing_key, verifying_key) = new_random_signing_keypair();
    let statement = fake_endorsement(digest, claim_types);
    let (endorsement, signature) = serialize_and_sign_endorsement(&statement, signing_key);
    (
        TransparentReleaseEndorsement {
            endorsement,
            subject: vec![],
            endorsement_signature: signature.as_bytes().to_vec(),
            rekor_log_entry: Vec::new(),
        },
        verifying_key,
    )
}

// Creates valid endorsements and matching reference values for an Oak
// Containers chain.
fn create_oc_endorsements_reference_values(
    extracted_evidence: &ExtractedEvidence,
) -> (Endorsements, ReferenceValues) {
    let oc_data = match extracted_evidence.evidence_values.as_ref().expect("no evidence values") {
        EvidenceValues::OakContainers(oc) => oc,
        _ => panic!("bad test setup"),
    };

    let kernel_layer = oc_data.kernel_layer.as_ref().expect("no kernel layer");
    let (stage1, stage1_vkey) =
        create_endorsement(kernel_layer.init_ram_fs.as_ref().expect("no init ram fs"), vec![]);
    let (memory_map, memory_map_vkey) =
        create_endorsement(kernel_layer.memory_map.as_ref().expect("no memory map"), vec![]);
    let (acpi, acpi_vkey) =
        create_endorsement(kernel_layer.acpi.as_ref().expect("no acpi"), vec![]);

    let (system_image, system_image_vkey) = create_endorsement(
        oc_data
            .system_layer
            .as_ref()
            .expect("no system layer")
            .system_image
            .as_ref()
            .expect("no system image"),
        vec![],
    );

    let container_layer_data = oc_data.container_layer.as_ref().expect("no container layer");
    let (container_binary, container_binary_vkey) =
        create_endorsement(container_layer_data.bundle.as_ref().expect("no bundle"), vec![]);

    let vcek_cert =
        fs::read(data_path(OC_VCEK_MILAN_CERT_DER)).expect("couldn't read VCEK Milan cert");
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };
    (
        Endorsements {
            r#type: Some(oak_proto_rust::oak::attestation::v1::endorsements::Type::OakContainers(
                OakContainersEndorsements {
                    root_layer: Some(RootLayerEndorsements {
                        tee_certificate: vcek_cert,
                        stage0: None,
                    }),
                    kernel_layer: Some(KernelLayerEndorsements {
                        kernel: None,
                        kernel_cmd_line: None,
                        init_ram_fs: Some(stage1),
                        memory_map: Some(memory_map),
                        acpi: Some(acpi),
                    }),
                    system_layer: Some(SystemLayerEndorsements {
                        system_image: Some(system_image),
                    }),
                    container_layer: Some(ContainerLayerEndorsements {
                        binary: Some(container_binary),
                        configuration: None,
                    }),
                },
            )),
            // TODO: b/375137648 - Populate `event_endorsements` proto field.
            event_endorsements: None,
        },
        ReferenceValues {
            r#type: Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
                root_layer: Some(RootLayerReferenceValues {
                    amd_sev: Some(AmdSevReferenceValues {
                        min_tcb_version: Some(TcbVersion { boot_loader: 3, tee: 0, snp: 20, microcode: 209 }),
                        allow_debug: false,
                        stage0: Some(skip.clone()),
                    }),
                    ..Default::default()
                }),
                kernel_layer: Some(KernelLayerReferenceValues {
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
                    init_ram_fs: Some(binary_reference_value_for_endorser_pk(stage1_vkey)),
                    memory_map: Some(binary_reference_value_for_endorser_pk(memory_map_vkey)),
                    acpi: Some(binary_reference_value_for_endorser_pk(acpi_vkey)),
                }),
                system_layer: Some(SystemLayerReferenceValues {
                    system_image: Some(binary_reference_value_for_endorser_pk(system_image_vkey)),
                }),
                container_layer: Some(ContainerLayerReferenceValues {
                    binary: Some(binary_reference_value_for_endorser_pk(container_binary_vkey)),
                    configuration: Some(skip.clone()),
                }),
            })),
        },
    )
}

// Creates valid endorsements and matching reference values for a restricted
// kernel application.
fn create_rk_endorsements_reference_values(
    extracted_evidence: &ExtractedEvidence,
) -> (Endorsements, ReferenceValues) {
    let rk_data = match extracted_evidence.evidence_values.as_ref().expect("no evidence values") {
        EvidenceValues::OakRestrictedKernel(rk) => rk,
        _ => panic!("bad test setup"),
    };

    let kernel_layer = rk_data.kernel_layer.as_ref().expect("no kernel layer");
    let (init_ram_fs, init_ram_fs_vkey) =
        create_endorsement(kernel_layer.init_ram_fs.as_ref().expect("no init ram fs"), vec![]);
    let (memory_map, memory_map_vkey) =
        create_endorsement(kernel_layer.memory_map.as_ref().expect("no memory map"), vec![]);
    let (acpi, acpi_vkey) =
        create_endorsement(kernel_layer.acpi.as_ref().expect("no acpi"), vec![]);

    let app_layer_data = rk_data.application_layer.as_ref().expect("no application layer");
    let (app_binary, app_binary_vkey) =
        create_endorsement(app_layer_data.binary.as_ref().expect("no binary"), vec![]);

    let vcek_cert = fs::read(data_path(RK_VCEK_MILAN_CERT_DER)).expect("couldn't read TEE cert");
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };
    (
        Endorsements {
            r#type: Some(
                oak_proto_rust::oak::attestation::v1::endorsements::Type::OakRestrictedKernel(
                    OakRestrictedKernelEndorsements {
                        root_layer: Some(RootLayerEndorsements {
                            tee_certificate: vcek_cert,
                            stage0: None,
                        }),
                        kernel_layer: Some(KernelLayerEndorsements {
                            kernel: None,
                            kernel_cmd_line: None,
                            init_ram_fs: Some(init_ram_fs),
                            memory_map: Some(memory_map),
                            acpi: Some(acpi),
                        }),
                        application_layer: Some(ApplicationLayerEndorsements {
                            binary: Some(app_binary),
                            configuration: None,
                        }),
                    },
                ),
            ),
            // TODO: b/375137648 - Populate `event_endorsements` proto field.
            event_endorsements: None,
        },
        ReferenceValues {
            r#type: Some(reference_values::Type::OakRestrictedKernel(
                OakRestrictedKernelReferenceValues {
                    root_layer: Some(RootLayerReferenceValues {
                        amd_sev: Some(AmdSevReferenceValues {
                            min_tcb_version: Some(TcbVersion {
                                boot_loader: 3,
                                tee: 0,
                                snp: 20,
                                microcode: 209,
                            }),
                            allow_debug: false,
                            stage0: Some(skip.clone()),
                        }),
                        ..Default::default()
                    }),
                    kernel_layer: Some(KernelLayerReferenceValues {
                        kernel: Some(KernelBinaryReferenceValue {
                            r#type: Some(kernel_binary_reference_value::Type::Skip(
                                SkipVerification {},
                            )),
                        }),
                        kernel_cmd_line_text: Some(TextReferenceValue {
                            r#type: Some(text_reference_value::Type::StringLiterals(
                                StringLiterals { value: vec![String::from("console=ttyS0")] },
                            )),
                        }),
                        init_ram_fs: Some(binary_reference_value_for_endorser_pk(init_ram_fs_vkey)),
                        memory_map: Some(binary_reference_value_for_endorser_pk(memory_map_vkey)),
                        acpi: Some(binary_reference_value_for_endorser_pk(acpi_vkey)),
                    }),
                    application_layer: Some(ApplicationLayerReferenceValues {
                        binary: Some(binary_reference_value_for_endorser_pk(app_binary_vkey)),
                        configuration: Some(skip.clone()),
                    }),
                },
            )),
        },
    )
}
