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

use anyhow::{Context, Error, anyhow};
use oak_attestation_verification_results::{
    unique_session_binding_public_key, unique_signing_public_key,
};
use oak_crypto::verifier::Verifier;
use oak_proto_rust::oak::attestation::v1::AttestationResults;
use p256::ecdsa::VerifyingKey;

/// Trait that allows extracting a verifying key (e.g., a session binding key)
/// from the supplied and verified evidence.
pub trait KeyExtractor: Send + Sync {
    /// Extracts the verifying key from the attestation results returned by
    /// [`AttestationVerifier`]. Only results of a successful verification are
    /// expected to contain the key.
    fn extract_verifying_key(
        &self,
        results: &AttestationResults,
    ) -> Result<Box<dyn Verifier>, Error>;
}

/// Key extractor that takes the key from the top level signing_public_key field
/// in [`AttestationResults`]
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

/// Key extractor that retrieves the binding key from the artifacts contained
/// in [`AttestationResults`].
pub struct DefaultBindingKeyExtractor;

impl KeyExtractor for DefaultBindingKeyExtractor {
    fn extract_verifying_key(
        &self,
        attestation_results: &AttestationResults,
    ) -> Result<Box<dyn Verifier>, Error> {
        let public_key = unique_session_binding_public_key(attestation_results)
            .map_err(|msg| anyhow::anyhow!(msg))
            .context("getting unique session binding public key")?;
        Ok(Box::new(VerifyingKey::from_sec1_bytes(public_key.as_slice()).map_err(|err| {
            anyhow!("couldn't create a verifying key from the session binding public key in the evidence: {}", err)
        })?))
    }
}

/// Key extractor that retrieves the binding key from the artifacts contained
/// in [`AttestationResults`].
pub struct EventLogSigningKeyExtractor;

impl KeyExtractor for EventLogSigningKeyExtractor {
    fn extract_verifying_key(
        &self,
        attestation_results: &AttestationResults,
    ) -> Result<Box<dyn Verifier>, Error> {
        let public_key = unique_signing_public_key(attestation_results)
            .map_err(|msg| anyhow::anyhow!(msg))
            .context("getting unique signing public key")?;
        Ok(Box::new(VerifyingKey::from_sec1_bytes(public_key.as_slice()).map_err(|err| {
            anyhow!(
                "couldn't create a verifying key from the signing public key in the evidence: {}",
                err
            )
        })?))
    }
}
