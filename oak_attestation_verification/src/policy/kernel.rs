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
use oak_time::Instant;

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

impl Policy<[u8]> for KernelPolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event =
            stage0_measurements_to_kernel_layer_data(decode_event_proto::<Stage0Measurements>(
                "type.googleapis.com/oak.attestation.v1.Stage0Measurements",
                evidence,
            )?);
        let endorsement: Option<KernelEndorsement> =
            endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_kernel_event_expected_values(
            verification_time.into_unix_millis(),
            endorsement.as_ref(),
            &self.reference_values,
        )
        .context("couldn't verify kernel endorsements")?;

        compare_kernel_layer_measurement_digests(&event, &expected_values)
            .context("couldn't verify kernel event")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use test_util::{get_oc_reference_values, get_rk_reference_values, AttestationData};

    use super::*;

    const KERNEL_EVENT_INDEX: usize = 0;

    #[test]
    fn verify_oc_success() {
        let d = AttestationData::load_milan_oc_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
        let endorsement = &d.endorsements.events[KERNEL_EVENT_INDEX];
        let ref_values = get_oc_reference_values(&d.reference_values);
        let policy = KernelPolicy::new(ref_values.kernel_layer.as_ref().unwrap());

        let result = policy.verify(d.make_valid_time(), event, endorsement);

        // TODO: b/356631062 - Verify detailed attestation results.
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn verify_rk_success() {
        let d: AttestationData = AttestationData::load_milan_rk_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
        let endorsement = &d.endorsements.events[KERNEL_EVENT_INDEX];
        let ref_values = get_rk_reference_values(&d.reference_values);
        let policy = KernelPolicy::new(ref_values.kernel_layer.as_ref().unwrap());

        let result = policy.verify(d.make_valid_time(), event, endorsement);

        // TODO: b/356631062 - Verify detailed attestation results.
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }
}
