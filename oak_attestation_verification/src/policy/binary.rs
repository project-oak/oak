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
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{EventAttestationResults, EventData, EventReferenceValues},
};
use oak_time::Instant;

use crate::{
    compare::compare_event_measurement_digests, expect::acquire_event_expected_values,
    util::decode_event_proto,
};

pub struct BinaryPolicy {
    reference_values: EventReferenceValues,
}

impl BinaryPolicy {
    pub fn new(reference_values: &EventReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for BinaryPolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        _endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<EventData>(
            "type.googleapis.com/oak.attestation.v1.EventData",
            evidence,
        )?;

        let expected_values = acquire_event_expected_values(
            verification_time.into_unix_millis(),
            &self.reference_values,
        )
        .context("acquiring event expected values")?;

        compare_event_measurement_digests(&event, &expected_values)
            .context("comparing event digests")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { ..Default::default() })
    }
}
