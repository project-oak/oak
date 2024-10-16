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

use oak_containers_sdk::{standalone::StandaloneOrchestrator, OrchestratorInterface};
use oak_proto_rust::oak::{
    attestation::v1::{
        binary_reference_value, kernel_binary_reference_value, reference_values,
        text_reference_value, BinaryReferenceValue, ContainerLayerReferenceValues, Digests,
        InsecureReferenceValues, KernelBinaryReferenceValue, KernelDigests,
        KernelLayerReferenceValues, OakContainersReferenceValues, ReferenceValues,
        RootLayerReferenceValues, Stage0Measurements, StringLiterals, SystemLayerReferenceValues,
        TextReferenceValue,
    },
    session::v1::EndorsedEvidence,
    RawDigest,
};
use prost::Message;
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
                ..Default::default()
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

pub async fn create_oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
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
    let endorsed_evidence = {
        let mut orchestrator = StandaloneOrchestrator::create_with_custom_config_and_measurements(
            stage0_measurements,
            stage1_system_image,
            application_image,
            application_config,
        )
        .expect("failed to create StandaloneOrchestrator");

        orchestrator.get_endorsed_evidence().await.expect("failed to get endorsed evidence")
    };

    (endorsed_evidence, reference_values)
}

/// Get the JSON representation of the endorsed evidence.
///
/// Use Protobuf/JSON mappings. This can be required in order to navigate the
/// data as a tree, which prost does not allow. This functionality is needed to
/// be able to effectively check for equality between proto messages while also
/// permitting exceptions.
pub async fn endorsed_evidence_as_json(
    endorsed_evidence: &EndorsedEvidence,
) -> anyhow::Result<serde_json::Value> {
    let input = endorsed_evidence.encode_to_vec();
    convert_binpb_to_json(input, "oak.session.v1.EndorsedEvidence").await
}

/// Get the JSON representation of the reference values.
///
/// Use Protobuf/JSON mappings. This can be required in order to navigate the
/// data as a tree, which prost does not allow. This functionality is needed to
/// be able to effectively check for equality between proto messages while also
/// permitting exceptions.
pub async fn reference_values_as_json(
    reference_values: &ReferenceValues,
) -> anyhow::Result<serde_json::Value> {
    let input = reference_values.encode_to_vec();
    convert_binpb_to_json(input, "oak.attestation.v1.ReferenceValues").await
}

/// Helper function to convert binary encoded protobuf messages to JSON using
/// the protobuf mappings.
/// Prost does not support this functionality, hence a CLI util is used.
async fn convert_binpb_to_json(
    input: Vec<u8>,
    type_name: &str,
) -> anyhow::Result<serde_json::Value> {
    // Create a temporary directory with symlinks for the relevant proto files in
    // the tempdir. This gives the CLI that converts binaryprotos to JSON access to
    // the needed schema, ensures that imports resolve, and avoids errors
    // related to compiling well known types.s
    let proto_dir = {
        let temp_dir = tempfile::tempdir()
            .map_err(|e| anyhow::anyhow!("Failed to create temporary directory: {}", e))?;

        let _ = tokio::process::Command::new("ln")
            .arg("-s")
            .arg(std::env::current_dir().unwrap().join("proto"))
            .arg(std::env::current_dir().unwrap().join("third_party"))
            .arg(temp_dir.path())
            .status()
            .await
            .map_err(|e| {
                anyhow::anyhow!(
                    "Failed to create symlinks for proto and third_party directories: {}",
                    e
                )
            })?;
        temp_dir
    };

    let mut converter_process = tokio::process::Command::new("buf")
        .arg("convert")
        .arg(proto_dir.path())
        .arg("--type")
        .arg(type_name)
        .arg("--from")
        .arg("-#format=binpb")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| anyhow::anyhow!("Failed to spawn buf command: {}", e))?;

    // Write the input to the converter_process's stdin
    if let Some(mut stdin) = converter_process.stdin.take() {
        tokio::io::AsyncWriteExt::write_all(&mut stdin, &input)
            .await
            .map_err(|e| anyhow::anyhow!("Failed to write to buf command stdin: {}", e))?;
    }

    // Read the output from the converter_process process's stdout
    let output = converter_process
        .wait_with_output()
        .await
        .map_err(|e| anyhow::anyhow!("Failed to wait for buf command: {}", e))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(anyhow::anyhow!("buf convert command failed: {}", stderr));
    }

    let json_string = String::from_utf8(output.stdout)
        .map_err(|e| anyhow::anyhow!("Failed to convert buf command output to UTF-8: {}", e))?;

    serde_json::from_str(&json_string).map_err(|e| anyhow::anyhow!("Failed to parse JSON: {}", e))
}

// Recursively remove properties from the current JSON tree that are not
// present in the previous JSON tree, and record the new properties. This can be
// helpful in order to assert equality on matching fields.
pub fn remove_new_properties(
    current: &mut serde_json::Value,
    previous: &serde_json::Value,
    path: &str,
) -> Vec<String> {
    let mut new_properties = Vec::new();
    match (current, previous) {
        (serde_json::Value::Object(current_obj), serde_json::Value::Object(previous_obj)) => {
            current_obj.retain(|key, value| {
                let new_path =
                    if path.is_empty() { format!("/{}", key) } else { format!("{}/{}", path, key) };
                if let Some(prev_value) = previous_obj.get(key) {
                    new_properties.extend(remove_new_properties(value, prev_value, &new_path));
                    true
                } else {
                    new_properties.push(new_path);
                    false
                }
            });
        }
        (serde_json::Value::Array(current_arr), serde_json::Value::Array(previous_arr)) => {
            for (index, (current_item, previous_item)) in
                current_arr.iter_mut().zip(previous_arr.iter()).enumerate()
            {
                let new_path = format!("{}/{}", path, index);
                new_properties.extend(remove_new_properties(
                    current_item,
                    previous_item,
                    &new_path,
                ));
            }
            if current_arr.len() > previous_arr.len() {
                new_properties.push(format!("{}/{}", path, previous_arr.len()));
                current_arr.truncate(previous_arr.len());
            }
        }
        _ => {}
    }
    new_properties
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn test_remove_new_properties_object() {
        let mut current = json!({
            "existing": "value",
            "new": "property"
        });
        let previous = json!({
            "existing": "value"
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!({"existing": "value"}));
        assert_eq!(new_properties, vec!["/new"]);
    }

    #[test]
    fn test_remove_new_properties_nested_object() {
        let mut current = json!({
            "nested": {
                "existing": "value",
                "new": "property"
            }
        });
        let previous = json!({
            "nested": {
                "existing": "value"
            }
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!({"nested": {"existing": "value"}}));
        assert_eq!(new_properties, vec!["/nested/new"]);
    }

    #[test]
    fn test_remove_new_properties_array() {
        let mut current = json!([1, 2, 3, 4]);
        let previous = json!([1, 2, 3]);
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!([1, 2, 3]));
        assert_eq!(new_properties, vec!["/3"]);
    }

    #[test]
    fn test_remove_new_properties_mixed() {
        let mut current = json!({
            "array": [1, 2, {"new": "item"}],
            "object": {"existing": "value", "new": "property"}
        });
        let previous = json!({
            "array": [1, 2],
            "object": {"existing": "value"}
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(
            current,
            json!({
                "array": [1, 2],
                "object": {"existing": "value"}
            })
        );
        assert_eq!(new_properties, vec!["/array/2", "/object/new"]);
    }

    #[test]
    fn test_remove_new_properties_whole_nested_object() {
        let mut current = json!({
            "existing": "value",
            "new_object": {
                "nested1": "value1",
                "nested2": "value2"
            }
        });
        let previous = json!({
            "existing": "value"
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!({"existing": "value"}));
        assert_eq!(new_properties, vec!["/new_object"]);
    }
}
