//
// Copyright 2026 The Project Oak Authors
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

use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{
        CbLayer1TransparentReferenceValues, CbLayer2TransparentReferenceValues,
        EventAttestationResults, KernelLayerReferenceValues,
    },
};
use oak_time::Instant;

/// Event policy for transparent stage 0.
///
/// This policy blindly succeeds when applied.
pub struct TransparentStage0Policy {
    _reference_values: KernelLayerReferenceValues,
}

impl TransparentStage0Policy {
    pub fn new(reference_values: &KernelLayerReferenceValues) -> Self {
        Self { _reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for TransparentStage0Policy {
    fn verify(
        &self,
        _verification_time: Instant,
        _evidence: &[u8],
        _endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        Ok(EventAttestationResults::default())
    }
}

/// Event policy for transparent layer 1.
///
/// This policy blindly succeeds when applied.
pub struct TransparentLayer1Policy {
    _reference_values: CbLayer1TransparentReferenceValues,
}

impl TransparentLayer1Policy {
    pub fn new(reference_values: &CbLayer1TransparentReferenceValues) -> Self {
        Self { _reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for TransparentLayer1Policy {
    fn verify(
        &self,
        _verification_time: Instant,
        _evidence: &[u8],
        _endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        Ok(EventAttestationResults::default())
    }
}

/// Event policy for transparent layer 2.
///
/// This policy blindly succeeds when applied.
pub struct TransparentLayer2Policy {
    _reference_values: CbLayer2TransparentReferenceValues,
}

impl TransparentLayer2Policy {
    pub fn new(reference_values: &CbLayer2TransparentReferenceValues) -> Self {
        Self { _reference_values: reference_values.clone() }
    }
}

impl Policy<[u8]> for TransparentLayer2Policy {
    fn verify(
        &self,
        _verification_time: Instant,
        _evidence: &[u8],
        _endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        Ok(EventAttestationResults::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_TIME: Instant = Instant::from_unix_millis(1_000_000);

    #[test]
    fn transparent_stage0_verify_succeeds() {
        let reference_values = KernelLayerReferenceValues::default();
        let policy = TransparentStage0Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, b"arbitrary evidence", &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
        assert_eq!(result.unwrap(), EventAttestationResults::default());
    }

    #[test]
    fn transparent_layer1_verify_succeeds() {
        let reference_values = CbLayer1TransparentReferenceValues::default();
        let policy = TransparentLayer1Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, b"arbitrary evidence", &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
        assert_eq!(result.unwrap(), EventAttestationResults::default());
    }

    #[test]
    fn transparent_layer2_verify_succeeds() {
        let reference_values = CbLayer2TransparentReferenceValues::default();
        let policy = TransparentLayer2Policy::new(&reference_values);

        let result = policy.verify(TEST_TIME, b"arbitrary evidence", &Variant::default());

        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
        assert_eq!(result.unwrap(), EventAttestationResults::default());
    }
}
