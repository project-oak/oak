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

#![no_std]

extern crate alloc;

use alloc::sync::Arc;

use oak_attestation_types::{
    assertion_generator::{AssertionGenerator, AssertionGeneratorError},
    attester::Attester,
    endorser::Endorser,
};
use oak_crypto::signer::Signer;
use oak_proto_rust::oak::attestation::v1::{Assertion, EndorsedEvidenceAssertion};
use prost::Message;

/// Wrapper that allows wrapping [`EndorsedEvidence`] into an assertion.
pub struct EndorsedEvidenceAssertionGenerator {
    // Attester generated the evidence.
    attester: Arc<dyn Attester>,
    // Endorser provides the endorsements for the evidence.
    endorser: Arc<dyn Endorser>,
    // The private counterpart of the key contained in the evidence allow signing of the arbitrary
    // data.
    signer: Arc<dyn Signer>,
}

impl EndorsedEvidenceAssertionGenerator {
    pub fn new(
        attester: Arc<dyn Attester>,
        endorser: Arc<dyn Endorser>,
        signer: Arc<dyn Signer>,
    ) -> Self {
        Self { attester, endorser, signer }
    }
}

impl AssertionGenerator for EndorsedEvidenceAssertionGenerator {
    // Legacy asserters use a different evidence model where the asserted data can
    // have complex structure (e.g., multiple application keys) and is defined as a
    // part of the evidence, so the callers don't have a control over it. For that
    // reason the symmetric verifier uses [`CompatAssertedDataExtractor`] to
    // identify the particular piece of the asserted data that is being verified.
    fn generate(&self, data: &[u8]) -> Result<Assertion, AssertionGeneratorError> {
        let evidence = self.attester.quote()?;
        let endorsements = self.endorser.endorse(Some(&evidence))?;
        let asserted_data_signature = self.signer.sign(data);
        let endorsed_evidence_assertion = EndorsedEvidenceAssertion {
            evidence: Some(evidence),
            endorsements: Some(endorsements),
            asserted_data_signature,
        };
        Ok(Assertion { content: endorsed_evidence_assertion.encode_to_vec() })
    }
}
