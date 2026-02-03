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

use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{
        ApplicationKeysData, ApplicationKeysReferenceValues, EventAttestationResults,
    },
};
use oak_time::Instant;

use crate::{
    results::{
        set_hybrid_encryption_public_key, set_session_binding_public_key, set_signing_public_key,
    },
    util::decode_event_proto,
};

pub struct ApplicationKeysPolicy {
    _reference_values: ApplicationKeysReferenceValues,
}

impl ApplicationKeysPolicy {
    pub fn new(reference_values: &ApplicationKeysReferenceValues) -> Self {
        Self { _reference_values: reference_values.clone() }
    }
}

// We have to use [`Policy<[u8]>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl Policy<[u8]> for ApplicationKeysPolicy {
    fn verify(
        &self,
        _verification_time: Instant,
        evidence: &[u8],
        _endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<ApplicationKeysData>(
            "type.googleapis.com/oak.attestation.v1.ApplicationKeysData",
            evidence,
        )?;

        // TODO: b/399885537 - Verify that the key is signed by the CA.

        let mut results = EventAttestationResults { ..Default::default() };
        if !event.session_binding_public_key.is_empty() {
            set_session_binding_public_key(&mut results, &event.session_binding_public_key);
        }
        if !event.hybrid_encryption_public_key.is_empty() {
            set_hybrid_encryption_public_key(&mut results, &event.hybrid_encryption_public_key);
        }
        if !event.signing_public_key.is_empty() {
            set_signing_public_key(&mut results, &event.signing_public_key);
        }

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(results)
    }
}
