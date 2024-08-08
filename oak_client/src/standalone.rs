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

//! Utilities for creating an [`OakClient`] instance that can interact with Oak
//! Standalone server instances.
//!
//! The Oak Standalone SDK allows easy development iteration and testing for an
//! Oak-enabled trusted binary without requiring the entire Oak containers
//! stack.
//!
//! Oak Standalone supports setting up an encrypted channel based on randomly
//! generated public keys.
//!
//! It does not currently support any sort of attestation flow.

use anyhow::Context;
use oak_proto_rust::oak::attestation::v1::{
    extracted_evidence, Endorsements, Evidence, ExtractedEvidence, OakStandaloneData,
};

use crate::verifier::AttestationVerifier;

/// An [`AttestationVerifier`] that performs no attestation verification, but
/// still receives the public key from the server to set up an encryption
/// channel.
///
/// This verifier should only be used during development and testing using the
/// Oak Standalone SDK featureset.
///
/// As we continually developing Oak Standalone, this implementation should
/// converge towards the standard implementation, and perhaps eventually be
/// removed completely.
#[derive(Default)]
pub struct StandaloneNoOpAttestationVerifier {}

impl StandaloneNoOpAttestationVerifier {
    pub fn new() -> Self {
        Self::default()
    }
}

impl AttestationVerifier for StandaloneNoOpAttestationVerifier {
    fn verify(&self, evidence: &Evidence, _: &Endorsements) -> anyhow::Result<ExtractedEvidence> {
        // Ignore everything about Evidence, Endorsements.
        // For this PoC, we just pull the key directly out of ApplicationKeys,
        // treating it as a plain old encryption key
        // TODO: b/347970899 - Rather than hard coding this, incorporate Oak Standalone
        // into the existing attestation verification framework.
        Ok(ExtractedEvidence {
            evidence_values: Some(extracted_evidence::EvidenceValues::Standalone(
                OakStandaloneData {},
            )),
            encryption_public_key: evidence
                .application_keys
                .as_ref()
                .context("no application key was present in the evidence")?
                .encryption_public_key_certificate
                .clone(),
            signing_public_key: vec![],
        })
    }
}
