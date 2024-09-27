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

use oak_attestation::dice::evidence_to_proto;
use oak_attestation_verification::verifier::{to_attestation_results, verify, verify_dice_chain};
use oak_containers_sdk::{standalone::StandaloneOrchestrator, OrchestratorInterface};
use oak_proto_rust::oak::{
    attestation::v1::{
        attestation_results::Status, binary_reference_value, endorsements,
        kernel_binary_reference_value, reference_values, text_reference_value,
        ApplicationLayerReferenceValues, BinaryReferenceValue, ContainerLayerReferenceValues,
        Digests, Endorsements, Event, EventLog, InsecureReferenceValues,
        KernelBinaryReferenceValue, KernelDigests, KernelLayerReferenceValues,
        OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerEndorsements,
        RootLayerReferenceValues, SkipVerification, Stage0Measurements, StringLiterals,
        SystemLayerReferenceValues, TextReferenceValue,
    },
    RawDigest,
};
use oak_restricted_kernel_sdk::attestation::EvidenceProvider;
use prost::Message;
use sha2::Digest;
use tokio;

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

#[test]
fn verify_mock_dice_chain() {
    let mock_evidence_provider = oak_restricted_kernel_sdk::testing::MockEvidenceProvider::create()
        .expect("failed to create mock provider");
    let mock_evidence = mock_evidence_provider.get_evidence();

    let result = verify_dice_chain(
        &evidence_to_proto(mock_evidence.clone()).expect("could not convert evidence to proto"),
    );

    assert!(result.is_ok());
    let evidence_values: oak_proto_rust::oak::attestation::v1::extracted_evidence::EvidenceValues =
        result.unwrap().evidence_values.unwrap();
    assert!(matches!(evidence_values, oak_proto_rust::oak::attestation::v1::extracted_evidence::EvidenceValues::OakRestrictedKernel{..}))
}

fn get_restricted_kernel_evidence_proto_with_eventlog()
-> oak_proto_rust::oak::attestation::v1::Evidence {
    let mock_evidence_provider = oak_restricted_kernel_sdk::testing::MockEvidenceProvider::create()
        .expect("failed to create mock provider");

    let mock_evidence = mock_evidence_provider.get_evidence();
    let mock_encoded_eventlog =
        mock_evidence_provider.get_encoded_event_log().expect("failed to get eventlog");
    let mock_eventlog =
        EventLog::decode(mock_encoded_eventlog).expect("Failed to decode EventLog proto");
    let mut mock_evidence_proto =
        evidence_to_proto(mock_evidence.clone()).expect("could not convert evidence to proto");
    let _ = mock_evidence_proto.event_log.insert(mock_eventlog);
    mock_evidence_proto
}

#[test]
fn verify_mock_dice_chain_with_valid_event_log() {
    let result = verify_dice_chain(&get_restricted_kernel_evidence_proto_with_eventlog());

    assert!(result.is_ok());
    let evidence_values: oak_proto_rust::oak::attestation::v1::extracted_evidence::EvidenceValues =
        result.unwrap().evidence_values.unwrap();
    assert!(matches!(evidence_values, oak_proto_rust::oak::attestation::v1::extracted_evidence::EvidenceValues::OakRestrictedKernel{..}))
}

#[test]
fn verify_mock_dice_chain_with_invalid_event_log() {
    let mut evidence = get_restricted_kernel_evidence_proto_with_eventlog();
    let encoded_stage0_event: &mut Vec<u8> = evidence
        .event_log
        .as_mut()
        .expect("there to be an eventlog")
        .encoded_events
        .iter_mut()
        .find(|encoded_event| {
            if let Ok(event) = Event::decode(encoded_event.as_slice()) {
                if let Some(event_any) = event.event {
                    event_any.type_url
                        == "type.googleapis.com/oak.attestation.v1.Stage0Measurements"
                } else {
                    false
                }
            } else {
                false
            }
        })
        .expect("there to be a stage0 event");

    let mut stage0 = Stage0Measurements::decode(encoded_stage0_event.as_slice()).ok().unwrap();
    stage0.kernel_cmdline = format!("evil modification {}", stage0.kernel_cmdline);
    *encoded_stage0_event = stage0.encode_to_vec();

    let result = verify_dice_chain(&evidence);

    assert!(result.is_err());
}

#[test]
fn verify_mock_restricted_kernel_evidence() {
    let mock_evidence_provider = oak_restricted_kernel_sdk::testing::MockEvidenceProvider::create()
        .expect("failed to create mock provider");
    let evidence = evidence_to_proto(mock_evidence_provider.get_evidence().clone())
        .expect("failed to convert evidence to proto");

    let endorsements = Endorsements {
        r#type: Some(endorsements::Type::OakRestrictedKernel(OakRestrictedKernelEndorsements {
            root_layer: Some(RootLayerEndorsements::default()),
            ..Default::default()
        })),
    };

    // reference values that skip everything.
    let reference_values = {
        let skip = BinaryReferenceValue {
            r#type: Some(binary_reference_value::Type::Skip(SkipVerification::default())),
        };
        ReferenceValues {
            r#type: Some(reference_values::Type::OakRestrictedKernel(
                OakRestrictedKernelReferenceValues {
                    root_layer: Some(RootLayerReferenceValues {
                        insecure: Some(InsecureReferenceValues::default()),
                        ..Default::default()
                    }),
                    #[allow(deprecated)]
                    kernel_layer: Some(KernelLayerReferenceValues {
                        kernel: Some(KernelBinaryReferenceValue {
                            r#type: Some(kernel_binary_reference_value::Type::Skip(
                                SkipVerification {},
                            )),
                        }),
                        kernel_image: None,
                        kernel_setup_data: None,
                        kernel_cmd_line: None,
                        kernel_cmd_line_regex: None,
                        kernel_cmd_line_text: Some(TextReferenceValue {
                            r#type: Some(text_reference_value::Type::Skip(SkipVerification {})),
                        }),
                        init_ram_fs: Some(skip.clone()),
                        memory_map: Some(skip.clone()),
                        acpi: Some(skip.clone()),
                    }),
                    application_layer: Some(ApplicationLayerReferenceValues {
                        binary: Some(skip.clone()),
                        configuration: Some(skip.clone()),
                    }),
                },
            )),
        }
    };

    let r = verify(NOW_UTC_MILLIS, &evidence, &endorsements, &reference_values);
    let p = to_attestation_results(&r);

    eprintln!("======================================");
    eprintln!("code={} reason={}", p.status, p.reason);
    eprintln!("======================================");
    assert!(r.is_ok());
    assert!(p.status() == Status::Success);
}

fn oak_containers_skip_all_reference_values() -> ReferenceValues {
    #[allow(deprecated)]
    ReferenceValues {
        r#type: Some(reference_values::Type::OakContainers(OakContainersReferenceValues {
            root_layer: Some(RootLayerReferenceValues {
                insecure: Some(InsecureReferenceValues::default()),
                ..Default::default()
            }),
            kernel_layer: Some(KernelLayerReferenceValues {
                kernel: Some(KernelBinaryReferenceValue {
                    r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
                }),
                kernel_setup_data: None,
                kernel_image: None,
                kernel_cmd_line: None,
                kernel_cmd_line_regex: None,
                kernel_cmd_line_text: Some(TextReferenceValue {
                    r#type: Some(text_reference_value::Type::Skip(SkipVerification {})),
                }),
                init_ram_fs: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                }),
                memory_map: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                }),
                acpi: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                }),
            }),
            system_layer: Some(SystemLayerReferenceValues {
                system_image: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                }),
            }),
            container_layer: Some(ContainerLayerReferenceValues {
                binary: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                }),
                configuration: Some(BinaryReferenceValue {
                    r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
                }),
            }),
        })),
    }
}

#[tokio::test]
async fn verify_mock_oak_containers_evidence() {
    // Create a mock orchestrator and get endorsed evidence
    let mut orchestrator = oak_containers_sdk::standalone::StandaloneOrchestrator::default();
    let endorsed_evidence =
        orchestrator.get_endorsed_evidence().await.expect("Failed to get endorsed evidence");

    let evidence = endorsed_evidence.evidence.as_ref().expect("No evidence found");
    let endorsements = endorsed_evidence.endorsements.as_ref().expect("No endorsements found");

    // Create reference values that skip all verifications
    let reference_values = oak_containers_skip_all_reference_values();

    // Perform verification
    let verification_result = verify(NOW_UTC_MILLIS, evidence, endorsements, &reference_values);
    let attestation_results = to_attestation_results(&verification_result);

    eprintln!("======================================");
    eprintln!("code={} reason={}", attestation_results.status, attestation_results.reason);
    eprintln!("======================================");
    // Assert verification success
    assert!(verification_result.is_ok(), "Verification failed");
    assert_eq!(attestation_results.status(), Status::Success, "Unexpected attestation status");
}

#[tokio::test]
async fn verify_mock_oak_containers_evidence_with_custom_evidence() {
    let stage0_digests = Stage0Measurements {
        setup_data_digest: vec![1u8; 32],
        kernel_measurement: vec![2u8; 32],
        ram_disk_digest: vec![3u8; 32],
        memory_map_digest: vec![4u8; 32],
        acpi_digest: vec![5u8; 32],
        kernel_cmdline: "custom kernel command line".to_string(),
    };
    let stage1_system_image = [6u8; 32];
    let application_image = [7u8; 32];
    let application_config = vec![8u8; 32];

    let (endorsed_evidence, reference_values) =
        oak_attestation_integration_test_utils::create_oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
            stage0_digests,
            &stage1_system_image,
            &application_image,
            application_config,
        )
        .await;

    let evidence = endorsed_evidence.evidence.as_ref().expect("No evidence found");
    let endorsements = endorsed_evidence.endorsements.as_ref().expect("No endorsements found");

    // Perform verification
    let verification_result = verify(NOW_UTC_MILLIS, evidence, endorsements, &reference_values);
    let attestation_results = to_attestation_results(&verification_result);

    eprintln!("======================================");
    eprintln!("code={} reason={}", attestation_results.status, attestation_results.reason);
    eprintln!("======================================");
    // Assert verification success
    assert!(verification_result.is_ok(), "Verification failed");
    assert_eq!(attestation_results.status(), Status::Success, "Unexpected attestation status");
}
