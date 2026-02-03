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
    attestation::v1::{BinaryReferenceValue, EventAttestationResults, FirmwareEndorsement},
};
use oak_time::Instant;

use crate::{
    compare::compare_firmware_layer_measurement_digests, expect::acquire_stage0_expected_values,
};

pub struct FirmwarePolicy {
    reference_values: BinaryReferenceValue,
}

impl FirmwarePolicy {
    pub fn new(reference_values: &BinaryReferenceValue) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

// Policy which verifies the firmware.
impl Policy<[u8]> for FirmwarePolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let endorsement: Option<FirmwareEndorsement> =
            endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_stage0_expected_values(
            verification_time.into_unix_millis(),
            endorsement.as_ref(),
            &self.reference_values,
        )
        .context("acquiring firmware expected values")?;

        compare_firmware_layer_measurement_digests(evidence, &expected_values)
            .context("comparing firmware digests")?;

        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use test_util::{AttestationData, extract_attestation_report, get_oc_reference_values};

    use super::*;

    #[test]
    fn verify_oc_succeeds() {
        let d = AttestationData::load_milan_oc_release();
        let measurement = &extract_attestation_report(&d.evidence).unwrap().data.measurement;
        let endorsement = d.endorsements.initial.as_ref().unwrap();
        let ref_values = get_oc_reference_values(&d.reference_values);
        let firmware_reference_values = ref_values
            .root_layer
            .as_ref()
            .unwrap()
            .amd_sev
            .as_ref()
            .unwrap()
            .stage0
            .as_ref()
            .unwrap();
        let policy = FirmwarePolicy::new(firmware_reference_values);

        let result = policy.verify(d.make_valid_time(), measurement, endorsement);

        // TODO: b/356631062 - Verify detailed attestation results.
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }
}
