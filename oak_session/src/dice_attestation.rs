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

use alloc::{boxed::Box, string::ToString};

use anyhow::anyhow;
use oak_attestation_verification::verifier::verify;
use oak_proto_rust::oak::attestation::v1::{
    attestation_results, AttestationResults, Endorsements, Evidence, ReferenceValues,
};
use p256::ecdsa::VerifyingKey;

use crate::{
    attestation::AttestationVerifier,
    clock::Clock,
    session_binding::{SessionBindingVerifier, SignatureBindingVerifierBuilder},
};

struct DiceAttestationVerifier {
    ref_values: ReferenceValues,
    clock: Box<dyn Clock>,
}

#[allow(dead_code)]
impl DiceAttestationVerifier {
    pub fn create(ref_values: ReferenceValues, clock: Box<dyn Clock>) -> Self {
        DiceAttestationVerifier { ref_values, clock }
    }
}

impl AttestationVerifier for DiceAttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        match verify(self.clock.get_current_time_ms(), evidence, endorsements, &self.ref_values) {
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

    fn create_session_binding_verifier(
        &self,
        results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn SessionBindingVerifier>> {
        // TODO: b/365745680 - replace with the session binding public key.
        let verifying_key = results
            .extracted_evidence
            .as_ref()
            .ok_or(anyhow!("missing signing public key in the evidence"))?
            .signing_public_key
            .clone();
        Ok(Box::new(SignatureBindingVerifierBuilder::default()
            .verifier(Box::new(VerifyingKey::from_sec1_bytes(verifying_key.as_slice())
                .map_err(|err|anyhow!(
                    "couldn't create a verifying key from the signing key in the evidence: {}",
                     err))?))
            .build()
            .map_err(|err|anyhow!("couldn't build signature binding verifier: {}", err))?))
    }
}
