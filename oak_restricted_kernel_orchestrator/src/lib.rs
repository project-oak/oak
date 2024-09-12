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

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

#[cfg(feature = "exchange_evidence")]
use oak_attestation::dice::evidence_and_event_log_to_proto;
use oak_channel::basic_framed::receive_raw;
#[cfg(feature = "exchange_evidence")]
use oak_channel::basic_framed::send_raw;
use oak_dice::evidence::Stage0DiceData;
use oak_proto_rust::oak::{
    attestation::v1::{ApplicationLayerData, EventLog},
    RawDigest,
};
use prost::Message;

use crate::alloc::string::ToString;

pub struct AttestedApp {
    pub elf_binary: alloc::vec::Vec<u8>,
    pub derived_key: oak_restricted_kernel_dice::DerivedKey,
    pub dice_data: oak_dice::evidence::RestrictedKernelDiceData,
    pub event_log: EventLog,
}

impl AttestedApp {
    pub fn load_and_attest<C: oak_channel::Channel>(
        mut channel: C,
        stage0_dice_data: Stage0DiceData,
        encoded_event_log: Vec<u8>,
    ) -> Self {
        let elf_binary = receive_raw::<C>(&mut channel).expect("failed to load");
        log::info!("Binary loaded, size: {}", elf_binary.len());
        let app_digest = oak_restricted_kernel_dice::measure_digest_sha2_256(&elf_binary);
        let application_layer_data = ApplicationLayerData {
            binary: Some(RawDigest { sha2_256: app_digest.to_vec(), ..Default::default() }),
            config: Some(RawDigest { ..Default::default() }),
        };
        let event = oak_proto_rust::oak::attestation::v1::Event {
            tag: "oak_restricted_kernel_orchestrator".to_string(),
            event: Some(prost_types::Any {
                type_url: "type.googleapis.com/oak.attestation.v1.ApplicationLayerData".to_string(),
                value: application_layer_data.encode_to_vec(),
            }),
        };
        let encoded_event: Vec<u8> = event.encode_to_vec();
        let event_digest = oak_restricted_kernel_dice::measure_digest_sha2_256(&encoded_event);
        log::info!(
            "Application digest (sha2-256): {}",
            app_digest.map(|x| alloc::format!("{:02x}", x)).join("")
        );
        let derived_key =
            oak_restricted_kernel_dice::generate_derived_key(&stage0_dice_data, &app_digest);
        let dice_data =
            oak_restricted_kernel_dice::generate_dice_data(stage0_dice_data, &event_digest);

        let mut event_log =
            EventLog::decode(encoded_event_log.as_slice()).expect("failed to decode event log");

        event_log.encoded_events.push(event.encode_to_vec());

        #[cfg(feature = "exchange_evidence")]
        {
            let evidence = evidence_and_event_log_to_proto(
                dice_data.evidence.clone(),
                Some(event_log.encode_to_vec().as_slice()),
            )
            .expect("failed to convert evidence to proto");
            send_raw(&mut channel, &evidence.encode_to_vec()).expect("failed to return evidence");
        }

        Self { elf_binary, derived_key, dice_data, event_log }
    }

    pub fn get_encoded_event_log(&self) -> Vec<u8> {
        self.event_log.encode_to_vec()
    }
}
