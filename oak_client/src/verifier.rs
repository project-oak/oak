//
// Copyright 2023 The Project Oak Authors
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
use oak_attestation_verification::verifier::verify_dice_chain_and_extract_evidence;
use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence, ExtractedEvidence};

pub trait AttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<ExtractedEvidence>;
}

/// Verifier that doesn't check the Evidence against Reference Values and only
/// checks the DICE chain correctness.
/// Should be only used for testing.
pub struct InsecureAttestationVerifier;

impl AttestationVerifier for InsecureAttestationVerifier {
    fn verify(&self, evidence: &Evidence, _: &Endorsements) -> anyhow::Result<ExtractedEvidence> {
        verify_dice_chain_and_extract_evidence(evidence).context("couldn't verify the DICE chain")
    }
}

pub fn extract_encryption_public_key(evidence: &Evidence) -> anyhow::Result<Vec<u8>> {
    let attestation_results = verify_dice_chain_and_extract_evidence(evidence)
        .context("couldn't verify the DICE chain")?;
    Ok(attestation_results.encryption_public_key)
}
