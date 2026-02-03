//
// Copyright 2022 The Project Oak Authors
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

#![no_std]

extern crate alloc;

pub use dice::LayerData;
use oak_attestation_types::attester::Attester;
use oak_proto_rust::oak::{
    RawDigest,
    attestation::v1::{EventLog, Evidence},
};
use p256::ecdsa::VerifyingKey;
use sha2::Digest;

pub mod dice;
pub mod public_key;

/// Attester that can build an Event Log but doesn't use attestation mechanisms
/// to sign the events. Can be used for tests or for use-cases that don't have
/// hardware-based attestation.
#[derive(Default)]
pub struct EventLogAttester {
    evidence: Evidence,
}

impl EventLogAttester {
    pub fn new() -> Self {
        Self { evidence: Evidence::default() }
    }
}

impl From<Evidence> for EventLogAttester {
    fn from(evidence: Evidence) -> Self {
        Self { evidence }
    }
}

impl Attester for EventLogAttester {
    /// Add an `encoded_event` to the [`EventLog`].
    fn extend(&mut self, encoded_event: &[u8]) -> anyhow::Result<()> {
        self.evidence
            .event_log
            .get_or_insert_with(EventLog::default)
            .encoded_events
            .push(encoded_event.to_vec());

        Ok(())
    }

    /// Get [`Evidence`] with the Event Log built using the `extend` function.
    fn quote(&self) -> anyhow::Result<Evidence> {
        Ok(self.evidence.clone())
    }
}

/// Deprecated trait that allow for explicitly adding application keys to the
/// attestation evidence.
#[deprecated = "Use application keys from the event log."]
pub trait ApplicationKeysAttester {
    // TODO: b/368030563 - Remove this trait once all client library instances use
    // the applications keys from the event log.

    /// Adds certificates representing the application keys to the attestation
    /// evidence.
    //
    /// This is an outdated approach that has been replaced by adding the
    /// applications keys to the event log. It is only retained for
    /// compatibility while some client deployments still expect this format.
    fn add_application_keys(
        self,
        layer_data: LayerData,
        kem_public_key: &[u8],
        verifying_key: &VerifyingKey,
        group_kem_public_key: Option<&[u8]>,
        group_verifying_key: Option<&VerifyingKey>,
    ) -> anyhow::Result<Evidence>;
}

pub trait MeasureDigest {
    fn measure_digest(self) -> RawDigest;
}

impl<T: bytes::Buf> MeasureDigest for T {
    fn measure_digest(mut self) -> RawDigest {
        let mut digest = sha2::Sha256::default();
        while self.remaining() > 0 {
            let chunk = self.chunk();
            digest.update(chunk);
            self.advance(chunk.len());
        }
        let digest_bytes: [u8; 32] = digest.finalize().into();
        RawDigest { sha2_256: digest_bytes.to_vec(), ..Default::default() }
    }
}

#[cfg(test)]
mod tests {
    use bytes::Buf;

    use super::*;

    #[test]
    fn test_digest_equivalency() {
        let buf1 = [1u8, 2, 3, 4, 5];
        let digest1 = buf1.measure_digest();

        let buf2 = [1u8, 2, 3].chain(&[4u8, 5][..]);
        let digest2 = buf2.measure_digest();

        assert_eq!(digest1, digest2);
    }
}
