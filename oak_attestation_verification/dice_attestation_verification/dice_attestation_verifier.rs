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

//! This module provides an implementation of the Attestation Verifier bases on
//! verifying the DICE chain.

#![no_std]

extern crate alloc;

use alloc::{string::ToString, sync::Arc};

use oak_attestation_verification::verifier::verify;
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::attestation::v1::{
    AttestationResults, Endorsements, Evidence, ReferenceValues, attestation_results,
};
use oak_time::Clock;

/// Attestation verifier verifying evidence produced by the DICE attestation.
///
/// DICE attestation is defined
/// [here](https://trustedcomputinggroup.org/wp-content/uploads/DICE-Attestation-Architecture-Version-1.1-Revision-18_pub.pdf).
/// Our approach to using DICE for the TEE attestation is described in
/// [this talk](https://assets-global.website-files.com/63c54a346e01f30e726f97cf/660e6af00e242f9c38cac561_DICE%20Attestation%20on%20AMD%20SEV-SNP%20-%20Juliette%20Pluto%20Ivan%20Petrov.pdf)
///
/// Deprecated and up for deletion - use AmdSevSnpAttestationVerifier instead.
pub struct DiceAttestationVerifier {
    ref_values: ReferenceValues,
    clock: Arc<dyn Clock>,
}

#[allow(dead_code)]
impl DiceAttestationVerifier {
    pub fn create(ref_values: ReferenceValues, clock: Arc<dyn Clock>) -> Self {
        DiceAttestationVerifier { ref_values, clock }
    }
}

impl AttestationVerifier for DiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let verification_time = self.clock.get_time();

        match verify(verification_time.into_unix_millis(), evidence, endorsements, &self.ref_values)
        {
            Ok(extracted_evidence) => Ok(AttestationResults {
                status: attestation_results::Status::Success.into(),
                extracted_evidence: Some(extracted_evidence),
                ..Default::default()
            }),
            Err(err) => Ok(AttestationResults {
                status: attestation_results::Status::GenericFailure.into(),
                reason: err.to_string(),
                ..Default::default()
            }),
        }
    }
}
