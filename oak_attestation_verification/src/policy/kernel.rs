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
        EventAttestationResults, KernelEndorsement, KernelLayerReferenceValues, Stage0Measurements,
    },
    Variant,
};

use crate::{
    compare::compare_kernel_layer_measurement_digests,
    expect::acquire_kernel_event_expected_values,
    extract::stage0_measurements_to_kernel_layer_data, util::decode_event_proto,
};

pub struct KernelPolicy {
    reference_values: KernelLayerReferenceValues,
}

impl KernelPolicy {
    pub fn new(reference_values: &KernelLayerReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<[u8], Variant> for KernelPolicy {
    fn verify(
        &self,
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let event =
            stage0_measurements_to_kernel_layer_data(decode_event_proto::<Stage0Measurements>(
                "type.googleapis.com/oak.attestation.v1.Stage0Measurements",
                encoded_event,
            )?);
        let endorsement: KernelEndorsement =
            encoded_endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_kernel_event_expected_values(
            milliseconds_since_epoch,
            Some(&endorsement),
            &self.reference_values,
        )
        .context("couldn't verify kernel endorsements")?;

        compare_kernel_layer_measurement_digests(&event, &expected_values)
            .context("couldn't verify kernel event")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { ..Default::default() })
    }
}
