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

use oak_attestation::dice::DiceAttester;
use oak_attestation_types::{
    attester::Attester,
    transparent_attester::TransparentAttester,
    util::{Serializable, encode_length_delimited_proto},
};
use oak_attestation_verification::verifier::{EventLogType, verify_dice_chain};
use oak_dice::evidence::TeePlatform;
use oak_proto_rust::oak::{RawDigest, attestation::v1::ApplicationLayerData};
use prost::Message;

const TEST_APPLICATION_DIGEST: [u8; 4] = [0, 1, 2, 3];
const TEST_TRANSPARENT_APPLICATION_DIGEST: [u8; 4] = [4, 5, 6, 7];

#[test]
fn dice_attester_generates_correct_dice_chain() {
    let stage0_dice_data_proto = oak_stage0_dice::generate_initial_dice_data(
        oak_stage0_dice::mock_attestation_report,
        TeePlatform::None,
    )
    .expect("couldn't create initial DICE data");
    let serialized_stage0_dice_data = encode_length_delimited_proto(&stage0_dice_data_proto);

    let mut dice_attester = DiceAttester::deserialize(&serialized_stage0_dice_data)
        .expect("couldn't deserialize attester");

    let test_stage0_measurements = oak_proto_rust::oak::attestation::v1::Stage0Measurements {
        setup_data_digest: vec![],
        kernel_measurement: vec![],
        ram_disk_digest: vec![],
        memory_map_digest: vec![],
        acpi_digest: vec![],
        kernel_cmdline: String::new(),
    };
    let stage0_event = oak_stage0_dice::encode_stage0_event(test_stage0_measurements);
    dice_attester.extend(&stage0_event).expect("couldn't extend attester evidence");

    let application_event = oak_proto_rust::oak::attestation::v1::Event {
        tag: "application_layer".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ApplicationLayerData".to_string(),
            value: ApplicationLayerData {
                binary: Some(RawDigest {
                    sha2_256: TEST_APPLICATION_DIGEST.to_vec(),
                    ..RawDigest::default()
                }),
                config: None,
            }
            .encode_to_vec(),
        }),
    };
    let encoded_application_event = application_event.encode_to_vec();
    dice_attester.extend(&encoded_application_event).expect("couldn't extend the evidence");

    let test_evidence = dice_attester.quote().expect("couldn't generate the evidence");
    let result = verify_dice_chain(&test_evidence, EventLogType::OriginalEventLog);
    assert!(result.is_ok());
}

#[test]
fn dice_attester_generates_correct_dice_chain_with_transparent_events() {
    let stage0_dice_data_proto = oak_stage0_dice::generate_initial_dice_data(
        oak_stage0_dice::mock_attestation_report,
        TeePlatform::None,
    )
    .expect("couldn't create initial DICE data");
    let serialized_stage0_dice_data = encode_length_delimited_proto(&stage0_dice_data_proto);

    let mut dice_attester = DiceAttester::deserialize(&serialized_stage0_dice_data)
        .expect("couldn't deserialize attester");

    let test_stage0_measurements = oak_proto_rust::oak::attestation::v1::Stage0Measurements {
        setup_data_digest: vec![],
        kernel_measurement: vec![],
        ram_disk_digest: vec![],
        memory_map_digest: vec![],
        acpi_digest: vec![],
        kernel_cmdline: String::new(),
    };
    let stage0_event = oak_stage0_dice::encode_stage0_event(test_stage0_measurements);

    let test_stage0_transparent_measurements =
        oak_proto_rust::oak::attestation::v1::Stage0TransparentMeasurements {
            setup_data_digest: vec![],
            kernel_measurement: vec![],
            ram_disk_digest: vec![],
            memory_map_digest: vec![],
            acpi_digest: vec![],
            kernel_cmdline_digest: vec![],
        };
    let stage0_trans_event =
        oak_stage0_dice::encode_stage0_transparent_event(test_stage0_transparent_measurements);

    dice_attester
        .extend_transparent(&stage0_event, &stage0_trans_event)
        .expect("couldn't extend attester evidence");

    let application_event = oak_proto_rust::oak::attestation::v1::Event {
        tag: "application_layer".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ApplicationLayerData".to_string(),
            value: ApplicationLayerData {
                binary: Some(RawDigest {
                    sha2_256: TEST_APPLICATION_DIGEST.to_vec(),
                    ..RawDigest::default()
                }),
                config: None,
            }
            .encode_to_vec(),
        }),
    };
    let encoded_application_event = application_event.encode_to_vec();

    // While there is no transparent event for the application layer, we reuse the
    // same `ApplicationLayerData` proto and create a new tag
    // "transparent_application_layer" to demonstrate the transparent event log is
    // generated and validated correctly.
    let transparent_application_event = oak_proto_rust::oak::attestation::v1::Event {
        tag: "transparent_application_layer".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.ApplicationLayerData".to_string(),
            value: ApplicationLayerData {
                binary: Some(RawDigest {
                    sha2_256: TEST_TRANSPARENT_APPLICATION_DIGEST.to_vec(),
                    ..RawDigest::default()
                }),
                config: None,
            }
            .encode_to_vec(),
        }),
    };
    let encoded_trans_application_event = transparent_application_event.encode_to_vec();

    dice_attester
        .extend_transparent(&encoded_application_event, &encoded_trans_application_event)
        .expect("couldn't extend the evidence");

    let test_evidence = dice_attester.quote().expect("couldn't generate the evidence");

    let original_result = verify_dice_chain(&test_evidence, EventLogType::OriginalEventLog)
        .expect("Failed to verify DICE Chain with original event log");
    let transparent_result = verify_dice_chain(&test_evidence, EventLogType::TransparentEventLog)
        .expect("Failed to verify DICE Chain with transparent event log");
    assert_eq!(original_result, transparent_result);

    let event_log = test_evidence.event_log.expect("no event log");
    let transparent_event_log =
        test_evidence.transparent_event_log.expect("no transparent event log");

    // Assert that the number of elements in each event log is 2.
    assert_eq!(transparent_event_log.encoded_events.len(), 2);
    assert_eq!(event_log.encoded_events.len(), 2);
}
