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

//! Contains code related to the policy that is combined from individual Event
//! policies and is used to verify the whole TEE software stack.

pub mod application;
pub mod binary;
pub mod kernel;
pub mod system;

use alloc::{boxed::Box, string::ToString, vec, vec::Vec};

use itertools::izip;
use oak_attestation_verification_types::policy::{EventPolicy, Policy};
use oak_proto_rust::oak::attestation::v1::{
    attestation_results::Status, AttestationResults, EventAttestationResults, EventEndorsements,
    EventLog,
};

/// Represents a combination of Event Policies.
///
/// They are represented as a list where each element corresponds to an `Event`
/// in the `EventLog` and `EventEndorsements` in the `EventEndorsementsLog` with
/// the same index. This means that mapping between Policies and Events is done
/// via ordering.
pub struct CombinedPolicy {
    policies: Vec<Box<dyn EventPolicy>>,
}

impl CombinedPolicy {
    pub fn new(policies: Vec<Box<dyn EventPolicy>>) -> Self {
        CombinedPolicy { policies }
    }
}

impl Policy for CombinedPolicy {
    fn verify(
        &self,
        event_log: &EventLog,
        event_endorsements: &EventEndorsements,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<AttestationResults> {
        if event_log.encoded_events.len() != event_endorsements.encoded_event_endorsements.len() {
            anyhow::bail!(
                "eventLog length ({}) is not equal to the EventEndorsementsLog length ({})",
                event_log.encoded_events.len(),
                event_endorsements.encoded_event_endorsements.len()
            );
        }
        if self.policies.len() != event_log.encoded_events.len() {
            anyhow::bail!(
                "number of Policies ({}) is not equal to the EventLog length ({})",
                self.policies.len(),
                event_log.encoded_events.len()
            );
        }

        let verification_iterator = izip!(
            self.policies.iter(),
            event_log.encoded_events.iter(),
            event_endorsements.encoded_event_endorsements.iter()
        );
        let event_attestation_results = verification_iterator
            .map(|(event_policy, event, event_endorsements)| {
                event_policy.verify(event, event_endorsements, milliseconds_since_epoch).unwrap_or(
                    // TODO: b/366186091 - Use Rust error types for failed attestation.
                    EventAttestationResults {},
                )
            })
            .collect::<Vec<EventAttestationResults>>();

        // TODO: b/366419879 - Combine per-event attestation results.
        #[allow(deprecated)]
        Ok(AttestationResults {
            status: Status::Unspecified.into(),
            reason: "".to_string(),
            encryption_public_key: vec![],
            signing_public_key: vec![],
            extracted_evidence: None,
            event_attestation_results,
        })
    }
}
