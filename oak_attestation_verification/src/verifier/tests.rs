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

use digest_util::raw_to_hex_digest;
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, extracted_evidence::EvidenceValues, kernel_binary_reference_value,
        reference_values, tcb_version_reference_value, text_reference_value, AmdSevReferenceValues,
        ApplicationLayerEndorsements, ApplicationLayerReferenceValues, BinaryReferenceValue,
        ContainerLayerEndorsements, ContainerLayerReferenceValues, Endorsements, ExtractedEvidence,
        KernelBinaryReferenceValue, KernelLayerEndorsements, KernelLayerReferenceValues,
        OakContainersEndorsements, OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerEndorsements,
        RootLayerReferenceValues, SkipVerification, StringLiterals, SystemLayerEndorsements,
        SystemLayerReferenceValues, TcbVersionReferenceValue, TextReferenceValue,
        TransparentReleaseEndorsement,
    },
    RawDigest,
};
use oak_sev_snp_attestation_report::AttestationReport;
use test_util::attestation_data::AttestationData;
use zerocopy::FromBytes;

use crate::{
    extract::extract_evidence,
    test_util::{
        binary_reference_value_for_endorser_pk, fake_endorsement, new_random_signing_keypair,
        serialize_and_sign_endorsement,
    },
    verifier::{to_attestation_results, verify, Status},
};

// Pretend the tests run at this time: 2025-10-01, 08:00 UTC. This date
// must be valid with respect to the period hardwired in
// test_util::fake_endorsement().
const NOW_UTC_MILLIS: i64 = 1_759_305_600_000;

#[test]
fn test_milan_oc_staging_success() {
    let d = AttestationData::load_milan_oc_staging();
    let extracted_evidence = extract_evidence(&d.evidence).expect("failed to extract evidence");
    let (endorsements, reference_values) =
        create_oc_endorsements_reference_values(&extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &d.evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

#[test]
fn test_milan_rk_staging_success() {
    let d = AttestationData::load_milan_rk_staging();
    let extracted_evidence = extract_evidence(&d.evidence).expect("failed to extract evidence");
    let (endorsements, reference_values) =
        create_rk_endorsements_reference_values(&extracted_evidence);

    let r = verify(NOW_UTC_MILLIS, &d.evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status as i32, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

fn create_endorsement(
    digest: &RawDigest,
    claim_types: Vec<&str>,
) -> (TransparentReleaseEndorsement, p256::PublicKey) {
    let hex_digest = raw_to_hex_digest(digest);
    let (signing_key, verifying_key) = new_random_signing_keypair();
    let statement = fake_endorsement(&hex_digest, claim_types);
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
#[allow(deprecated)]
fn create_oc_endorsements_reference_values(
    extracted_evidence: &ExtractedEvidence,
) -> (Endorsements, ReferenceValues) {
    let d = AttestationData::load_milan_oc_staging();
    let vcek_cert = d.get_tee_certificate().expect("failed to get VCEK cert");
    let report = AttestationReport::ref_from_bytes(
        &d.evidence.root_layer.as_ref().unwrap().remote_attestation_report,
    )
    .expect("failed to get report");
    let tcb_version_struct = report.data.get_reported_tcb_version();
    let tcb_version = oak_proto_rust::oak::attestation::v1::TcbVersion {
        boot_loader: tcb_version_struct.boot_loader.into(),
        tee: tcb_version_struct.tee.into(),
        snp: tcb_version_struct.snp.into(),
        microcode: tcb_version_struct.microcode.into(),
        fmc: tcb_version_struct.fmc.into(),
    };

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
            // TODO: b/375137648 - Populate `events` proto field.
            ..Default::default()
        },
        ReferenceValues {
            r#type: Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
                root_layer: Some(RootLayerReferenceValues {
                    amd_sev: Some(AmdSevReferenceValues {
                        min_tcb_version: Some(tcb_version),
                        milan: Some(TcbVersionReferenceValue { r#type: Some(tcb_version_reference_value::Type::Minimum(tcb_version)) }),
                        genoa: Some(TcbVersionReferenceValue { r#type: Some(tcb_version_reference_value::Type::Minimum(tcb_version)) }),
                        turin: Some(TcbVersionReferenceValue { r#type: Some(tcb_version_reference_value::Type::Minimum(tcb_version)) }),
                        allow_debug: false,
                        check_vcek_cert_expiry: true,
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
#[allow(deprecated)]
fn create_rk_endorsements_reference_values(
    extracted_evidence: &ExtractedEvidence,
) -> (Endorsements, ReferenceValues) {
    let d = AttestationData::load_milan_rk_staging();
    let vcek_cert = d.get_tee_certificate().expect("failed to get VCEK cert");
    let report = AttestationReport::ref_from_bytes(
        &d.evidence.root_layer.as_ref().unwrap().remote_attestation_report,
    )
    .expect("failed to get report");
    let tcb_version_struct = report.data.get_reported_tcb_version();
    let tcb_version = oak_proto_rust::oak::attestation::v1::TcbVersion {
        boot_loader: tcb_version_struct.boot_loader.into(),
        tee: tcb_version_struct.tee.into(),
        snp: tcb_version_struct.snp.into(),
        microcode: tcb_version_struct.microcode.into(),
        fmc: tcb_version_struct.fmc.into(),
    };

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
            // TODO: b/375137648 - Populate `events` proto field.
            ..Default::default()
        },
        ReferenceValues {
            r#type: Some(reference_values::Type::OakRestrictedKernel(
                OakRestrictedKernelReferenceValues {
                    root_layer: Some(RootLayerReferenceValues {
                        amd_sev: Some(AmdSevReferenceValues {
                            min_tcb_version: Some(tcb_version),
                            milan: Some(TcbVersionReferenceValue {
                                r#type: Some(tcb_version_reference_value::Type::Minimum(
                                    tcb_version,
                                )),
                            }),
                            genoa: Some(TcbVersionReferenceValue {
                                r#type: Some(tcb_version_reference_value::Type::Minimum(
                                    tcb_version,
                                )),
                            }),
                            turin: Some(TcbVersionReferenceValue {
                                r#type: Some(tcb_version_reference_value::Type::Minimum(
                                    tcb_version,
                                )),
                            }),
                            allow_debug: false,
                            check_vcek_cert_expiry: true,
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
