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

use oak_attestation_integration_tests::{Snapshot, SnapshotPath, create};
use oak_attestation_verification::verifier::{
    to_attestation_results, verify, verify_dice_chain_and_extract_evidence,
};
use oak_proto_rust::oak::attestation::{
    self,
    v1::{
        ApplicationLayerReferenceValues, BinaryReferenceValue, ContainerLayerReferenceValues,
        Endorsements, Event, InsecureReferenceValues, KernelBinaryReferenceValue,
        KernelLayerReferenceValues, OakContainersReferenceValues, OakRestrictedKernelEndorsements,
        OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerEndorsements,
        RootLayerReferenceValues, SkipVerification, Stage0Measurements, SystemLayerReferenceValues,
        TextReferenceValue, attestation_results::Status, binary_reference_value, endorsements,
        kernel_binary_reference_value, reference_values, text_reference_value,
    },
};
use oak_restricted_kernel_sdk::Attester;
use oak_sdk_standalone::Standalone;
use prost::Message;

// Pretend the tests run at this time: 1 Nov 2023, 9:00 UTC
const NOW_UTC_MILLIS: i64 = 1698829200000;

#[test]
fn verify_mock_dice_chain() {
    let mock_attester = oak_restricted_kernel_sdk::testing::MockAttester::create()
        .expect("failed to create mock attester");
    let mock_evidence = mock_attester.quote().expect("couldn't get evidence");

    let result = verify_dice_chain_and_extract_evidence(&mock_evidence);

    assert!(result.is_ok());
    let evidence_values: attestation::v1::extracted_evidence::EvidenceValues =
        result.unwrap().evidence_values.unwrap();
    assert!(matches!(
        evidence_values,
        attestation::v1::extracted_evidence::EvidenceValues::OakRestrictedKernel { .. }
    ))
}

fn get_restricted_kernel_evidence_proto_with_eventlog() -> attestation::v1::Evidence {
    let mock_attester = oak_restricted_kernel_sdk::testing::MockAttester::create()
        .expect("failed to create mock attester");
    mock_attester.quote().expect("couldn't get evidence")
}

#[test]
fn verify_mock_dice_chain_with_valid_event_log() {
    let result = verify_dice_chain_and_extract_evidence(
        &get_restricted_kernel_evidence_proto_with_eventlog(),
    );

    assert!(result.is_ok());
    let evidence_values: attestation::v1::extracted_evidence::EvidenceValues =
        result.unwrap().evidence_values.unwrap();
    assert!(matches!(
        evidence_values,
        attestation::v1::extracted_evidence::EvidenceValues::OakRestrictedKernel { .. }
    ))
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

    let result = verify_dice_chain_and_extract_evidence(&evidence);

    assert!(result.is_err());
}

#[test]
fn verify_mock_restricted_kernel_evidence() {
    let mock_attester = oak_restricted_kernel_sdk::testing::MockAttester::create()
        .expect("failed to create mock attester");
    let evidence = mock_attester.quote().expect("couldn't get mock evidence");

    let endorsements = Endorsements {
        r#type: Some(endorsements::Type::OakRestrictedKernel(OakRestrictedKernelEndorsements {
            root_layer: Some(RootLayerEndorsements::default()),
            ..Default::default()
        })),
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
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
                    kernel_layer: Some(KernelLayerReferenceValues {
                        kernel: Some(KernelBinaryReferenceValue {
                            r#type: Some(kernel_binary_reference_value::Type::Skip(
                                SkipVerification {},
                            )),
                        }),
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
    let endorsed_evidence = Standalone::builder()
        .build()
        .expect("failed to build standalone elements")
        .endorsed_evidence();

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
        create::oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
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

#[tokio::test]
async fn verify_mock_oak_containers_evidence_with_fuzzed_measurements() {
    use rand_chacha::ChaCha8Rng;
    use rand_core::{RngCore, SeedableRng};

    // We use a seed for determinsitic randomness.
    const SEED: u64 = 42; // The answer to it all.

    // Helper function to generate random bytes with fixed length of 32 bytes.
    fn random_sha2_256_digest() -> Vec<u8> {
        let mut rng = ChaCha8Rng::seed_from_u64(SEED);
        let mut bytes = vec![0u8; 32];
        rng.fill_bytes(&mut bytes);
        bytes
    }

    // Helper function to generate random bytes with random length.
    fn random_bytes() -> Vec<u8> {
        const MAX_RANDOM_BYTES_LENGTH: usize = 64;
        let mut rng = ChaCha8Rng::seed_from_u64(SEED);
        let length = rng.next_u32() as usize % MAX_RANDOM_BYTES_LENGTH + 1; // Random length between 1 and MAX_RANDOM_BYTES_LENGTH
        let mut bytes = vec![0u8; length];
        rng.fill_bytes(&mut bytes);
        bytes
    }

    // Generate a variety of measurements.
    for _ in 0..10 {
        let stage0_digests = Stage0Measurements {
            setup_data_digest: random_sha2_256_digest(),
            kernel_measurement: random_sha2_256_digest(),
            ram_disk_digest: random_sha2_256_digest(),
            memory_map_digest: random_sha2_256_digest(),
            acpi_digest: random_sha2_256_digest(),
            kernel_cmdline: String::from_utf8_lossy(&random_bytes()).to_string(),
        };
        let stage1_system_image = random_bytes();
        let application_image = random_bytes();
        let application_config = random_bytes();

        let (endorsed_evidence, reference_values) =
            create::oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
                stage0_digests,
                &stage1_system_image,
                &application_image,
                application_config,
            )
            .await;

        let evidence = endorsed_evidence.evidence.as_ref().expect("No evidence found");
        let endorsements = endorsed_evidence.endorsements.as_ref().expect("No endorsements found");

        let verification_result = verify(NOW_UTC_MILLIS, evidence, endorsements, &reference_values);
        let attestation_results = to_attestation_results(&verification_result);

        assert!(verification_result.is_ok(), "Verification failed for fuzzed measurements");
        assert_eq!(
            attestation_results.status(),
            Status::Success,
            "Unexpected attestation status for fuzzed measurements"
        );
    }
}

/// Assert that there are no breaking changes to the verification library.
///
/// Effectively it simulates a client running the current version of the
/// verification library, encountering attesation outputs created by an older
/// version of the attestation logic.
///
/// It does this by:
/// 1. Loading snapshots of old attestation outputs (created by previous
///    versions of our attestation logic).
/// 2. Running the current version of the verification library against each
///    snapshot.
/// 3. Asserting that verification succeeds every time.
#[tokio::test]
async fn test_verification_against_snapshots() {
    let most_recent_snapshot =
        SnapshotPath::most_recent().await.expect("Failed to get most recent snapshot");

    for snapshot_path in most_recent_snapshot.rev() {
        let snapshot =
            Snapshot::read_from_path(&snapshot_path).await.expect("Failed to read snapshot");

        let evidence = snapshot.endorsed_evidence.evidence.as_ref().expect("No evidence found");
        let endorsements =
            snapshot.endorsed_evidence.endorsements.as_ref().expect("No endorsements found");

        let verification_result =
            verify(NOW_UTC_MILLIS, evidence, endorsements, &snapshot.reference_values);
        let attestation_results = to_attestation_results(&verification_result);

        assert!(
            verification_result.is_ok(),
            "Verification failed for snapshot in {:?}",
            snapshot_path.dirname()
        );
        assert_eq!(
            attestation_results.status(),
            Status::Success,
            "Unexpected attestation status for snapshot in {:?}",
            snapshot_path.dirname()
        );
    }
}
