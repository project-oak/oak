//
// Copyright 2023 The Project Oak Authors
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

#![feature(iterator_try_collect)]
#![feature(never_type)]

use ciborium::Value;
use coset::cwt::ClaimName;
use oak_dice::cert::SHA2_256_ID;
use oak_proto_rust::oak::attestation::v1::{DiceData, Event, SystemLayerData};
use prost::Message;

pub fn stage0_dice_data_into_dice_attester(
    stage0_dice_data: oak_dice::evidence::Stage0DiceData,
    eventlog: oak_proto_rust::oak::attestation::v1::EventLog,
) -> anyhow::Result<oak_attestation::dice::DiceAttester> {
    let dice_data: DiceData =
        oak_attestation::dice::stage0_dice_data_and_event_log_to_proto(stage0_dice_data, eventlog)?;
    dice_data.try_into()
}

pub fn get_layer_data(system_image: &[u8]) -> oak_attestation::dice::LayerData {
    let digest = oak_attestation::dice::MeasureDigest::measure_digest(&system_image);
    let event = Event {
        tag: "stage1".to_string(),
        event: Some(prost_types::Any {
            type_url: "type.googleapis.com/oak.attestation.v1.SystemLayerData".to_string(),
            value: SystemLayerData { system_image: Some(digest.clone()) }.encode_to_vec(),
        }),
    };
    let encoded_event = event.encode_to_vec();
    let event_digest =
        oak_attestation::dice::MeasureDigest::measure_digest(&encoded_event.as_slice());
    oak_attestation::dice::LayerData {
        additional_claims: vec![(
            ClaimName::PrivateUse(oak_dice::cert::EVENT_ID),
            Value::Map(vec![(
                Value::Integer(SHA2_256_ID.into()),
                Value::Bytes(event_digest.sha2_256),
            )]),
        )],
        encoded_event,
    }
}
