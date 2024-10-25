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
use oak_attestation_types::{attester::Attester, util::Serializable};
use oak_attestation_verification::verifier::verify_dice_chain;
use oak_dice::evidence::TeePlatform;
use oak_proto_rust::oak::{attestation::v1::ApplicationLayerData, RawDigest};
use prost::Message;

const TEST_APPLICATION_DIGEST: [u8; 4] = [0, 1, 2, 3];

#[test]
fn dice_attester_generates_correct_dice_chain() {
    let stage0_dice_data_proto = oak_stage0_dice::generate_initial_dice_data(
        oak_stage0_dice::mock_attestation_report,
        TeePlatform::None,
    )
    .expect("couldn't create initial DICE data");
    let serialized_stage0_dice_data = stage0_dice_data_proto.encode_length_delimited_to_vec();

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
    let result = verify_dice_chain(&test_evidence);
    assert!(result.is_ok());
}
