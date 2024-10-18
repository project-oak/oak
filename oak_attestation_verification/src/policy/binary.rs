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

use anyhow::Context;
use oak_attestation_verification_types::policy::EventPolicy;
use oak_proto_rust::oak::attestation::v1::{
    EventAttestationResults, EventData, EventReferenceValues,
};

use crate::{
    expect::get_event_expected_values, util::decode_event_proto,
    verifier::compare_event_measurement_digests,
};

pub struct BinaryPolicy {
    reference_values: EventReferenceValues,
}

impl BinaryPolicy {
    pub fn new(reference_values: &EventReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl EventPolicy for BinaryPolicy {
    fn verify(
        &self,
        encoded_event: &[u8],
        _encoded_event_endorsement: &[u8],
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<EventData>(
            "type.googleapis.com/oak.attestation.v1.EventData",
            encoded_event,
        )?;

        // TODO: b/369821273 - Add clocks to policies.
        let expected_values = get_event_expected_values(0i64, &self.reference_values)
            .context("couldn't verify event endosements")?;
        compare_event_measurement_digests(&event, &expected_values)
            .context("couldn't verify generic event")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults {})
    }
}
