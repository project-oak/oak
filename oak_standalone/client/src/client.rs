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

use anyhow::Context;
use oak_client::{
    client::OakClient,
    transport::{EvidenceProvider, Transport},
    verifier::AttestationVerifier,
};
use oak_proto_rust::oak::attestation::v1::{
    extracted_evidence, Endorsements, Evidence, ExtractedEvidence, OakStandaloneData,
};
/// An [AttestationVerifier] that skips attestation, but still receives the
/// public key from the server to set up an encryption channel.
struct StandaloneAttestationVerifier {}

impl AttestationVerifier for StandaloneAttestationVerifier {
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

/// Create a new [OakClient] instance that is meant to interact with an Oak
/// Standalone server facade.
///
/// Attestation will not be verified, but the server should provide an
/// encryption PK that can be used to establish a crypto channel.
pub async fn new<T: Transport + EvidenceProvider>(transport: T) -> anyhow::Result<OakClient<T>> {
    let verifier = StandaloneAttestationVerifier {};
    OakClient::create(transport, &verifier).await
}
