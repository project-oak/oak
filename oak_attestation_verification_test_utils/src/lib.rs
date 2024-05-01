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

use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, extracted_evidence::EvidenceValues, kernel_binary_reference_value,
        reference_values, root_layer_data::Report, text_reference_value, AmdSevReferenceValues,
        ApplicationLayerReferenceValues, BinaryReferenceValue, ContainerLayerReferenceValues,
        Digests, ExtractedEvidence, InsecureReferenceValues, KernelBinaryReferenceValue,
        KernelDigests, KernelLayerData, KernelLayerReferenceValues, OakContainersReferenceValues,
        OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerData,
        RootLayerReferenceValues, SkipVerification, StringLiterals, SystemLayerReferenceValues,
        TcbVersion, TextReferenceValue,
    },
    RawDigest,
};

// Creates valid reference values for an Oak Containers chain.
pub fn create_containers_reference_values() -> ReferenceValues {
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
pub fn create_rk_reference_values() -> ReferenceValues {
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

pub fn reference_values_from_evidence(evidence: ExtractedEvidence) -> ReferenceValues {
    let r#type = match evidence.evidence_values.expect("no evidence") {
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
        EvidenceValues::Cb(_) => panic!("not yet supported"),
    };
    ReferenceValues { r#type }
}

pub fn root_layer_reference_values_from_evidence(
    root_layer: RootLayerData,
) -> RootLayerReferenceValues {
    let amd_sev = root_layer.report.clone().and_then(|report| match report {
        Report::SevSnp(r) => Some(AmdSevReferenceValues {
            min_tcb_version: r.current_tcb,
            stage0: Some(BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Digests(Digests {
                    digests: vec![RawDigest {
                        sha2_384: r.initial_measurement,
                        ..Default::default()
                    }],
                })),
            }),
            allow_debug: r.debug,
        }),
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

pub fn kernel_layer_reference_values_from_evidence(
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
        kernel_setup_data: None,
        kernel_image: None,
        kernel_cmd_line: None,
        kernel_cmd_line_regex: None,
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
