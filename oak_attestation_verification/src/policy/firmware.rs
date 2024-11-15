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
use oak_proto_rust::oak::attestation::v1::{
    BinaryReferenceValue, EventAttestationResults, FirmwareEndorsement,
};

use crate::{
    compare::compare_measurement_digest, expect::get_stage0_expected_values,
    platform::convert_amd_sev_snp_initial_measurement,
};

pub struct FirmwarePolicy {
    reference_values: BinaryReferenceValue,
}

impl FirmwarePolicy {
    pub fn new(reference_values: &BinaryReferenceValue) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

impl Policy<[u8], FirmwareEndorsement> for FirmwarePolicy {
    fn verify(
        &self,
        firmware_measurement: &[u8],
        _firmware_endorsement: &FirmwareEndorsement,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let initial_measurement = convert_amd_sev_snp_initial_measurement(firmware_measurement);
        let initial_measurement_expected_values = get_stage0_expected_values(
            milliseconds_since_epoch,
            // TODO: b/375137648 - Use firmware endorsement, once we switch to new endorsment
            // types.
            None,
            &self.reference_values,
        )
        .context("getting stage0 values")?;

        compare_measurement_digest(&initial_measurement, &initial_measurement_expected_values)
            .context("stage0 measurement values failed verification")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults {})
    }
}
