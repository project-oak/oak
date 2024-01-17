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
use oak_attestation_verification::{
    proto::oak::attestation::v1::{Endorsements, Evidence},
    verifier::{verify_dice_chain, AttestationVerifier, DiceChainResult},
};

/// Verifier that doesn't check the Evidence against Reference Values and only checks the DICE chain
/// correctness.
/// Should be only used for testing.
pub struct InsecureAttestationVerifier;

impl AttestationVerifier for InsecureAttestationVerifier {
    fn verify(&self, evidence: &Evidence, _: &Endorsements) -> anyhow::Result<DiceChainResult> {
        verify_dice_chain(evidence).context("couldn't verify the DICE chain")
    }
}
