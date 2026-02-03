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
    RawDigest,
    attestation::v1::{
        BinaryReferenceValue, ContainerLayerReferenceValues, Digests, InsecureReferenceValues,
        KernelBinaryReferenceValue, KernelDigests, KernelLayerReferenceValues,
        OakContainersReferenceValues, ReferenceValues, RootLayerReferenceValues,
        Stage0Measurements, StringLiterals, SystemLayerReferenceValues, TextReferenceValue,
        binary_reference_value, kernel_binary_reference_value, reference_values,
        text_reference_value,
    },
    session::v1::EndorsedEvidence,
};
use oak_sdk_standalone::Standalone;
use sha2::Digest;

/// Creates reference values that match the supplied digests and images
fn reference_values_for_oak_containers_measurements(
    stage0_measurements: &Stage0Measurements,
    stage1_system_image: &[u8],
    application_image: &[u8],
    application_config: &[u8],
) -> ReferenceValues {
    ReferenceValues {
        r#type: Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
            root_layer: Some(RootLayerReferenceValues {
                insecure: Some(InsecureReferenceValues::default()),
                ..Default::default()
            }),
            kernel_layer: Some(KernelLayerReferenceValues {
                kernel: Some(KernelBinaryReferenceValue {
                    r#type: Some(kernel_binary_reference_value::Type::Digests(KernelDigests {
                        image: Some(Digests {
                            digests: vec![RawDigest {
                                sha2_256: stage0_measurements.kernel_measurement.clone(),
                                ..Default::default()
                            }],
                        }),
                        setup_data: Some(Digests {
                            digests: vec![RawDigest {
                                sha2_256: stage0_measurements.setup_data_digest.clone(),
                                ..Default::default()
                            }],
                        }),
                    })),
                }),
                kernel_cmd_line_text: Some(TextReferenceValue {
                    r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                        value: vec![stage0_measurements.kernel_cmdline.clone()],
                    })),
                }),
                init_ram_fs: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: stage0_measurements.ram_disk_digest.clone(),
                            ..Default::default()
                        }],
                    })),
                }),
                memory_map: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: stage0_measurements.memory_map_digest.clone(),
                            ..Default::default()
                        }],
                    })),
                }),
                acpi: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: stage0_measurements.acpi_digest.clone(),
                            ..Default::default()
                        }],
                    })),
                }),
            }),
            system_layer: Some(SystemLayerReferenceValues {
                system_image: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: sha2::Sha256::digest(stage1_system_image).to_vec(),
                            ..Default::default()
                        }],
                    })),
                }),
            }),
            container_layer: Some(ContainerLayerReferenceValues {
                binary: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: sha2::Sha256::digest(application_image).to_vec(),
                            ..Default::default()
                        }],
                    })),
                }),
                configuration: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Digests(Digests {
                        digests: vec![RawDigest {
                            sha2_256: sha2::Sha256::digest(application_config).to_vec(),
                            ..Default::default()
                        }],
                    })),
                }),
            }),
        })),
    }
}

pub async fn oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
    stage0_measurements: Stage0Measurements,
    stage1_system_image: &[u8],
    application_image: &[u8],
    application_config: Vec<u8>,
) -> (EndorsedEvidence, ReferenceValues) {
    let reference_values = reference_values_for_oak_containers_measurements(
        &stage0_measurements,
        stage1_system_image,
        application_image,
        &application_config,
    );
    let standalone = Standalone::builder()
        .stage0_measurements(stage0_measurements)
        .stage1_system_image(stage1_system_image)
        .application_image(application_image)
        .application_config(application_config)
        .build()
        .expect("failed to create Standalone");

    (standalone.endorsed_evidence(), reference_values)
}
