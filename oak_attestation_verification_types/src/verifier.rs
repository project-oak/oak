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

use oak_proto_rust::oak::attestation::v1::{AttestationResults, Endorsements, Evidence};

/// Trait that provides the functionality for appraising the attestation
/// evidence and endorsements and producing attestation results.
///
/// <https://datatracker.ietf.org/doc/html/rfc9334#name-verifier>
#[cfg_attr(test, automock)]
pub trait AttestationVerifier: Send + Sync {
    /// Verifies an attestation given as endorsed evidence.
    ///
    /// Args:
    ///   evidence: The evidence that is about to be verified.
    ///   endorsements: The endorsements that are about to be verified.
    ///
    /// Returns:
    ///   Ok whenever the attestation verification succeeded. In that case,
    ///   the `AttestationResults`` payload is passed back to the caller which
    ///   contains status == SUCCESS and empty reason.
    ///
    /// TODO: b/356629314 - Deduplicate the error in the Result and the status
    /// in AttestationResults.
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults>;
}
