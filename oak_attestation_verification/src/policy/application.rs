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
    ApplicationLayerData, ApplicationLayerEndorsements, ApplicationLayerReferenceValues,
    EventAttestationResults,
};

use crate::{
    compare::compare_application_layer_measurement_digests,
    expect::get_application_layer_expected_values,
    util::{decode_event_endorsement_proto, decode_event_proto},
};

pub struct ApplicationPolicy {
    reference_values: ApplicationLayerReferenceValues,
}

impl ApplicationPolicy {
    pub fn new(reference_values: &ApplicationLayerReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl EventPolicy for ApplicationPolicy {
    fn verify(
        &self,
        encoded_event: &[u8],
        encoded_event_endorsement: &[u8],
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<ApplicationLayerData>(
            "type.googleapis.com/oak.attestation.v1.ApplicationLayerData",
            encoded_event,
        )?;
        let event_endorsements = decode_event_endorsement_proto::<ApplicationLayerEndorsements>(
            "type.googleapis.com/oak.attestation.v1.ApplicationLayerEndorsements",
            encoded_event_endorsement,
        )?;

        let expected_values = get_application_layer_expected_values(
            // TODO: b/369821273 - Add clocks to policies.
            0i64,
            Some(&event_endorsements),
            &self.reference_values,
        )
        .context("couldn't verify application endosements")?;
        compare_application_layer_measurement_digests(&event, &expected_values)
            .context("couldn't verify application event")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults {})
    }
}
