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

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    attestation::v1::{
        BinaryReferenceValue, EventAttestationResults, FirmwareEndorsement,
        RootLayerReferenceValues,
    },
    Variant,
};

use crate::{
    compare::compare_firmware_layer_measurement_digests, expect::acquire_stage0_expected_values,
    platform::convert_amd_sev_snp_initial_measurement,
};

pub struct FirmwarePolicy {
    reference_values: BinaryReferenceValue,
}

impl FirmwarePolicy {
    pub fn new(reference_values: &BinaryReferenceValue) -> Self {
        Self { reference_values: reference_values.clone() }
    }

    // TODO: b/398859203 - Remove this function once old reference values have been
    // updated.
    pub fn from_root_layer_reference_values(
        root_layer: &RootLayerReferenceValues,
    ) -> anyhow::Result<Self> {
        let firmware_reference_values = root_layer
            .amd_sev
            .as_ref()
            .context("AMD SEV-SNP attestation report wasn't provided")?
            .stage0
            .as_ref()
            .context("firmware measurement wasn't provided")?;
        Ok(Self::new(firmware_reference_values))
    }
}

impl Policy<[u8]> for FirmwarePolicy {
    fn verify(
        &self,
        firmware_measurement: &[u8],
        encoded_endorsement: &Variant,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let endorsement: Option<FirmwareEndorsement> =
            encoded_endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_stage0_expected_values(
            milliseconds_since_epoch,
            endorsement.as_ref(),
            &self.reference_values,
        )
        .context("getting firmware layer values")?;

        compare_firmware_layer_measurement_digests(firmware_measurement, &expected_values)
            .context("couldn't verify firmware layer")?;

        // This setup is used by CB until they implement their own firmware policy.
        let initial_measurement = convert_amd_sev_snp_initial_measurement(firmware_measurement);
        const FIRMWARE_MEASUREMENT_ARTIFACT_KEY: &str = "firmware_measurement";
        let mut artifacts = BTreeMap::<String, Vec<u8>>::new();
        artifacts.insert(
            FIRMWARE_MEASUREMENT_ARTIFACT_KEY.to_string(),
            initial_measurement.sha2_384.to_vec(),
        );
        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { artifacts })
    }
}
