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

use oak_proto_rust::oak::{Variant, attestation::v1::EventAttestationResults};
use oak_time::Instant;

/// A verification policy takes generic evidence and endorsement and performs
/// verification. Policies represent individual steps inside a verifier.
///
/// The notion of policy corresponds to the "Appraisal Policy for Evidence"
/// provided by the RATS standard:
/// <https://datatracker.ietf.org/doc/html/rfc9334#section-8.5>
pub trait Policy<V: ?Sized>: Send + Sync {
    /// Invokes the policy on the given inputs.
    ///
    /// Args:
    ///   verification_time: Expresses when the verification happens.
    ///   evidence: The evidence from an event, encoded as `V`, that is about
    ///       to be verified. `V` is `[u8]`` in most cases, but it doesn't
    ///       have to be that way.
    ///   endorsement: The endorsement to be included in the verification.
    ///       The endorsement is encoded as Variant.
    ///
    /// Returns:
    ///   Ok whenever the policy verification succeeded. In that case, the
    ///   EventAttestationResults payload is passed back for processing by
    ///   the attestation verifier.
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &V,
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults>;
}

/// Policy that takes an byte-encoded event with accompanying encoded
/// endorsement and performs attestation verification for this specific event.
pub trait EventPolicy = Policy<[u8]>;
