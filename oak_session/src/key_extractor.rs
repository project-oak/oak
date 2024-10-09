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

//! Trait for extracting a session binding key from the attestation result to
//! use for verifying session bindings.

use alloc::boxed::Box;

use anyhow::{anyhow, Error};
use oak_crypto::verifier::Verifier;
use oak_proto_rust::oak::attestation::v1::AttestationResults;
use p256::ecdsa::VerifyingKey;

pub trait KeyExtractor: Send {
    fn extract_verifying_key(
        &self,
        results: &AttestationResults,
    ) -> Result<Box<dyn Verifier>, Error>;
}

pub struct DefaultSigningKeyExtractor;

impl KeyExtractor for DefaultSigningKeyExtractor {
    fn extract_verifying_key(
        &self,
        results: &AttestationResults,
    ) -> Result<Box<dyn Verifier>, Error> {
        // TODO: b/365745680 - replace with the session binding public key.
        let verifying_key = results
            .extracted_evidence
            .as_ref()
            .ok_or(anyhow!("missing signing public key in the evidence"))?
            .signing_public_key
            .clone();
        Ok(Box::new(VerifyingKey::from_sec1_bytes(verifying_key.as_slice()).map_err(|err| {
            anyhow!("couldn't create a verifying key from the signing key in the evidence: {}", err)
        })?))
    }
}
