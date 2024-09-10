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

//! Contains code related to attestation verification policies.

use oak_proto_rust::oak::attestation::v1::{
    AttestationResults, Endorsements, EventAttestationResults, EventLog,
};

/// Verification Policy that takes an EventLog and corresponding Event
/// Endorsements and performs attestation verification.
///
/// Verification Policy correspond to the "Appraisal Policy for Evidence"
/// provided by the RATS standard.
/// <https://datatracker.ietf.org/doc/html/rfc9334#section-8.5>
pub trait Policy {
    fn verify(
        event_log: &EventLog,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults>;
}

/// Verification Policy that takes a serialized Event and a serialized Event
/// Endorsement and performs attestation verification for this specific Event.
pub trait EventPolicy {
    fn verify(
        &self,
        serialized_event: &[u8],
        serialized_event_endorsements: &[u8],
    ) -> anyhow::Result<EventAttestationResults>;
}
