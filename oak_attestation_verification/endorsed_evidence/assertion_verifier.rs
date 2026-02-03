//
// Copyright 2025 The Project Oak Authors
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

//! This module provides a compatibility [`AssertionVerifier`] to allow the use
//! of legacy attestation verification traits with assertions.

use alloc::boxed::Box;

use anyhow::anyhow;
use oak_attestation_verification_types::{
    assertion_verifier::{AssertionVerifier, AssertionVerifierError},
    verifier::AttestationVerifier,
};
use oak_proto_rust::oak::attestation::v1::{
    Assertion, EndorsedEvidenceAssertion, attestation_results::Status,
};
use oak_time::Instant;
use prost::Message;

use crate::key_extractor::KeyExtractor;

/// Wrapper that allows using legacy [`AttestationVerifier`] with a new
/// assertion format.
pub struct EndorsedEvidenceAssertionVerifier {
    pub attestation_verifier: Box<dyn AttestationVerifier>,
    pub key_extractor: Box<dyn KeyExtractor>,
}

impl AssertionVerifier for EndorsedEvidenceAssertionVerifier {
    fn verify(
        &self,
        assertion: &Assertion,
        asserted_data: &[u8],
        _verification_time: Instant,
    ) -> Result<(), AssertionVerifierError> {
        let endorsed_evidence_assertion =
            EndorsedEvidenceAssertion::decode(assertion.content.as_slice())?;
        let attestation_results = self.attestation_verifier.verify(
            &endorsed_evidence_assertion.evidence.ok_or(
                AssertionVerifierError::AssertionMissingExpectedFields {
                    error_msg: "no evidence in the endorsed evidence assertion".to_string(),
                },
            )?,
            &endorsed_evidence_assertion.endorsements.ok_or(
                AssertionVerifierError::AssertionMissingExpectedFields {
                    error_msg: "no endorsements in the endorsed evidence assertion".to_string(),
                },
            )?,
        )?;
        match attestation_results.status.try_into().map_err(|_| {
            AssertionVerifierError::Other(anyhow!(
                "unknown status in the attestation results: {}",
                attestation_results.status
            ))
        })? {
            Status::Success => {
                let verifying_key =
                    self.key_extractor.extract_verifying_key(&attestation_results)?;
                Ok(verifying_key.verify(
                    asserted_data,
                    endorsed_evidence_assertion.asserted_data_signature.as_slice(),
                )?)
            }
            Status::GenericFailure => Err(anyhow!(
                "Endorsed evidence verification failed: {}",
                attestation_results.reason
            )
            .into()),
            Status::Unspecified => {
                Err(anyhow!("Endorsed evidence verification failed with unspecified status").into())
            }
        }
    }
}
