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
    attestation::v1::{
        ApplicationEndorsement, ApplicationLayerData, ApplicationLayerReferenceValues,
        EventAttestationResults,
    },
    Variant,
};

use crate::{
    compare::compare_application_layer_measurement_digests,
    expect::acquire_application_event_expected_values, util::decode_event_proto,
};

pub struct ApplicationPolicy {
    reference_values: ApplicationLayerReferenceValues,
}

impl ApplicationPolicy {
    pub fn new(reference_values: &ApplicationLayerReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl Policy<[u8]> for ApplicationPolicy {
    fn verify(
        &self,
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<ApplicationLayerData>(
            "type.googleapis.com/oak.attestation.v1.ApplicationLayerData",
            encoded_event,
        )?;
        let endorsement: Option<ApplicationEndorsement> =
            encoded_endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_application_event_expected_values(
            milliseconds_since_epoch,
            endorsement.as_ref(),
            &self.reference_values,
        )
        .context("couldn't verify application endorsements")?;

        compare_application_layer_measurement_digests(&event, &expected_values)
            .context("couldn't verify application event")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { ..Default::default() })
    }
}
