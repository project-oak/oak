//
// Copyright 2025 The Project Oak Authors
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

/// Focus is on protocol buffer acrobatics without introducing any additional
/// dependencies.
use anyhow::Context;
use oak_proto_rust::oak::{
    RawDigest,
    attestation::v1::{
        AmdSevReferenceValues, ApplicationLayerEndorsements, ApplicationLayerReferenceValues,
        BinaryReferenceValue, CbReferenceValues, ContainerLayerEndorsements,
        ContainerLayerReferenceValues, Digests, Endorsements, Evidence, ExtractedEvidence,
        InsecureReferenceValues, KernelBinaryReferenceValue, KernelDigests, KernelLayerData,
        KernelLayerEndorsements, KernelLayerReferenceValues, OakContainersEndorsements,
        OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerData, RootLayerEndorsements,
        RootLayerReferenceValues, SkipVerification, StringLiterals, SystemLayerEndorsements,
        SystemLayerReferenceValues, TcbVersion, TcbVersionReferenceValue, TextReferenceValue,
        binary_reference_value, endorsements, extracted_evidence::EvidenceValues,
        kernel_binary_reference_value, reference_values, root_layer_data::Report,
        tcb_version_reference_value, text_reference_value,
    },
};
use oak_sev_snp_attestation_report::AttestationReport;
use zerocopy::FromBytes;

// Creates mock endorsements for an Oak Containers chain.
pub fn create_oc_endorsements(vcek_cert: &[u8]) -> Endorsements {
    let root_layer = RootLayerEndorsements { tee_certificate: vcek_cert.to_vec(), stage0: None };
    let kernel_layer = KernelLayerEndorsements {
        kernel: None,
        kernel_cmd_line: None,
        init_ram_fs: None,
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

// Creates mock endorsements for a restricted kernel application.
pub fn create_rk_endorsements(vcek_cert: &[u8]) -> Endorsements {
    let root_layer = RootLayerEndorsements { tee_certificate: vcek_cert.to_vec(), stage0: None };
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
        r#type: Some(endorsements::Type::OakRestrictedKernel(ends)),
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
    }
}

// Creates trivial but valid reference values for an Oak Containers chain
// All endorsements are skipped with the exception of the one which happens
// to be available via `endorsement_data`.
pub fn create_oc_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };
    // Assume this TCB version fits all attestation examples relying on the
    // present reference values.
    let tcb_version = TcbVersion { boot_loader: 3, tee: 0, snp: 20, microcode: 209, fmc: 0 };
    let tcb_version_ref_value = TcbVersionReferenceValue {
        r#type: Some(tcb_version_reference_value::Type::Minimum(tcb_version)),
    };

    #[allow(deprecated)]
    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: None,
        milan: Some(tcb_version_ref_value),
        genoa: Some(tcb_version_ref_value),
        turin: Some(tcb_version_ref_value),
        allow_debug: false,
        check_vcek_cert_expiry: true,
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

// Creates trivial but valid reference values for a restricted kernel
// application. Almost all configurable checks are bypassed.
pub fn create_rk_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };
    // Assume this TCB version fits all attestation examples relying on the
    // present reference values.
    let tcb_version = TcbVersion { boot_loader: 3, tee: 0, snp: 20, microcode: 209, fmc: 0 };
    let tcb_version_ref_value = TcbVersionReferenceValue {
        r#type: Some(tcb_version_reference_value::Type::Minimum(tcb_version)),
    };

    #[allow(deprecated)]
    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: None,
        milan: Some(tcb_version_ref_value),
        genoa: Some(tcb_version_ref_value),
        turin: Some(tcb_version_ref_value),
        allow_debug: false,
        check_vcek_cert_expiry: true,
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

/// Adds `InsecureReferenceValues` to the given reference values.
pub fn allow_insecure(reference_values: &mut ReferenceValues) {
    match reference_values.r#type.as_mut() {
        Some(reference_values::Type::OakContainers(r)) => {
            let root = r.root_layer.as_mut().unwrap();
            root.insecure = Some(InsecureReferenceValues {});
        }
        Some(reference_values::Type::OakRestrictedKernel(r)) => {
            let root = r.root_layer.as_mut().unwrap();
            root.insecure = Some(InsecureReferenceValues {});
        }
        _ => panic!("malformed reference values"),
    }
}

/// Creates digest-based reference values for extracted evidence.
pub fn create_reference_values_for_extracted_evidence(
    extracted_evidence: ExtractedEvidence,
) -> ReferenceValues {
    let r#type = match extracted_evidence.evidence_values.expect("no evidence") {
        EvidenceValues::OakRestrictedKernel(rk) => {
            let application = rk.application_layer.expect("no application layer evidence");
            let config = application.config.expect("no application config digest");
            Some(reference_values::Type::OakRestrictedKernel(OakRestrictedKernelReferenceValues {
                root_layer: Some(root_layer_reference_values_from_evidence(
                    rk.root_layer.expect("no root layer evidence"),
                )),
                kernel_layer: Some(kernel_layer_reference_values_from_evidence(
                    rk.kernel_layer.expect("no kernel layer evidence"),
                )),
                application_layer: Some(ApplicationLayerReferenceValues {
                    binary: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![
                                application.binary.expect("no application binary digest"),
                            ],
                        })),
                    }),
                    // We don't currently specify configuration values for Oak Containers
                    // applications, so skip for now if the sha2_256 value is empty.
                    configuration: if config.sha2_256.is_empty() {
                        Some(BinaryReferenceValue {
                            r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                        })
                    } else {
                        Some(BinaryReferenceValue {
                            r#type: Some(binary_reference_value::Type::Digests(Digests {
                                digests: vec![config],
                            })),
                        })
                    },
                }),
            }))
        }
        EvidenceValues::OakContainers(oc) => {
            let system = oc.system_layer.expect("no system layer evidence");
            let container = oc.container_layer.expect("no container layer evidence");
            Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
                root_layer: Some(root_layer_reference_values_from_evidence(
                    oc.root_layer.expect("no root layer evidence"),
                )),
                kernel_layer: Some(kernel_layer_reference_values_from_evidence(
                    oc.kernel_layer.expect("no kernel layer evidence"),
                )),
                system_layer: Some(SystemLayerReferenceValues {
                    system_image: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![system.system_image.expect("no system image digest")],
                        })),
                    }),
                }),
                container_layer: Some(ContainerLayerReferenceValues {
                    binary: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![container.bundle.expect("no container bundle digest")],
                        })),
                    }),
                    configuration: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(Digests {
                            digests: vec![container.config.expect("no container config digest")],
                        })),
                    }),
                }),
            }))
        }
        #[allow(deprecated)]
        EvidenceValues::Cb(_) => panic!("not yet supported"),
        EvidenceValues::Standalone(_) => panic!("not yet supported"),
    };
    ReferenceValues { r#type }
}

fn root_layer_reference_values_from_evidence(
    root_layer: RootLayerData,
) -> RootLayerReferenceValues {
    #[allow(deprecated)]
    let amd_sev = root_layer.report.clone().and_then(|report| match report {
        Report::SevSnp(r) => {
            let tcb = r.reported_tcb.unwrap();
            let rv = TcbVersionReferenceValue {
                r#type: Some(tcb_version_reference_value::Type::Minimum(tcb)),
            };

            Some(AmdSevReferenceValues {
                min_tcb_version: Some(tcb),
                milan: Some(rv),
                genoa: Some(rv),
                turin: Some(rv),
                stage0: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_384: r.initial_measurement,
                            ..Default::default()
                        }],
                    })),
                }),
                allow_debug: r.debug,
                check_vcek_cert_expiry: true,
            })
        }
        _ => None,
    });
    let intel_tdx = if let Some(Report::Tdx(_)) = root_layer.report.clone() {
        panic!("not yet supported");
    } else {
        None
    };
    let insecure = root_layer.report.and_then(|report| match report {
        Report::Fake(_) => Some(InsecureReferenceValues {}),
        _ => None,
    });
    RootLayerReferenceValues { amd_sev, intel_tdx, insecure }
}

fn kernel_layer_reference_values_from_evidence(
    kernel_layer: KernelLayerData,
) -> KernelLayerReferenceValues {
    #[allow(deprecated)]
    KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Digests(KernelDigests {
                image: Some(Digests {
                    digests: vec![kernel_layer.kernel_image.expect("no kernel image digest")],
                }),
                setup_data: Some(Digests {
                    digests: vec![
                        kernel_layer.kernel_setup_data.expect("no kernel setup data digest"),
                    ],
                }),
            })),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![kernel_layer.kernel_raw_cmd_line.expect("no kernel command-line")],
            })),
        }),
        init_ram_fs: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![kernel_layer.init_ram_fs.expect("no initial ram disk digest")],
            })),
        }),
        memory_map: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![kernel_layer.memory_map.expect("no memory map digest")],
            })),
        }),
        acpi: Some(BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Digests(Digests {
                digests: vec![kernel_layer.acpi.expect("no acpi digest")],
            })),
        }),
    }
}

/// Shorthand to extract Oak Containers reference values subtype.
pub fn get_oc_reference_values(reference_values: &ReferenceValues) -> OakContainersReferenceValues {
    let oc_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakContainers(containers_reference_values)) => {
            containers_reference_values.clone()
        }
        _ => panic!("no Oak Containers reference values"),
    };
    assert!(oc_reference_values.root_layer.is_some());
    assert!(
        oc_reference_values.root_layer.as_ref().unwrap().amd_sev.is_some()
            || oc_reference_values.root_layer.as_ref().unwrap().intel_tdx.is_some()
    );
    assert!(oc_reference_values.kernel_layer.is_some());
    assert!(oc_reference_values.system_layer.is_some());
    assert!(oc_reference_values.container_layer.is_some());
    oc_reference_values
}

/// Shorthand to extract Oak Restricted Kernel reference values subtype.
pub fn get_rk_reference_values(
    reference_values: &ReferenceValues,
) -> OakRestrictedKernelReferenceValues {
    let rk_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::OakRestrictedKernel(rk_reference_values)) => {
            rk_reference_values.clone()
        }
        _ => panic!("no Oak Restricted Kernel reference values"),
    };
    assert!(rk_reference_values.root_layer.is_some());
    assert!(rk_reference_values.kernel_layer.is_some());
    assert!(rk_reference_values.application_layer.is_some());
    rk_reference_values
}

/// Shorthand to extract CB reference values subtype.
pub fn get_cb_reference_values(reference_values: &ReferenceValues) -> CbReferenceValues {
    #[allow(deprecated)]
    let cb_reference_values = match reference_values.r#type.as_ref() {
        Some(reference_values::Type::Cb(cb_reference_values)) => cb_reference_values.clone(),
        _ => panic!("no CB reference values"),
    };
    assert!(cb_reference_values.root_layer.is_some());
    assert!(cb_reference_values.root_layer.as_ref().unwrap().amd_sev.is_some());
    assert!(!cb_reference_values.layers.is_empty());
    cb_reference_values
}

/// Shorthand to extract AMD attestation report from an AMD SEV-SNP evidence.
pub fn extract_attestation_report(evidence: &Evidence) -> anyhow::Result<&AttestationReport> {
    let root_layer =
        &evidence.root_layer.as_ref().context("root DICE layer wasn't provided in the evidence")?;
    AttestationReport::ref_from_bytes(&root_layer.remote_attestation_report)
        .map_err(|err| anyhow::anyhow!("invalid AMD SEV-SNP attestation report: {}", err))
}
