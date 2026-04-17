// Copyright 2026 The Project Oak Authors
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

//! Dummy attestation implementations for testing only.
//!
//! Provides no-op implementations of the Oak attestation traits, allowing
//! SelfUnidirectional sessions to complete the handshake without real
//! attestation infrastructure. This module should only be used in tests.

use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::attestation::v1::{
    AttestationResults, Endorsements, Evidence, OakContainersEndorsements,
    attestation_results::Status, endorsements::Type,
};
use oak_session::{
    attestation::AttestationType,
    config::SessionConfig,
    handshake::HandshakeType,
    session_binding::{SessionBinder, SessionBindingVerifier, SessionBindingVerifierProvider},
};

/// The attestation ID used for dummy attestation.
pub const DUMMY_ATTESTATION_ID: &str = "dummy";

/// The expected dummy certificate bytes shared between attester and verifier.
const DUMMY_EVIDENCE_CERTIFICATE: &[u8] = b"dummy-evidence-hello-world";

/// Creates a server-side `SessionConfig` using dummy attestation for testing.
pub fn dummy_server_session_config() -> SessionConfig {
    SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
        .add_self_attester(DUMMY_ATTESTATION_ID.to_string(), Box::new(DummyAttester))
        .add_self_endorser(DUMMY_ATTESTATION_ID.to_string(), Box::new(DummyEndorser))
        .add_session_binder(DUMMY_ATTESTATION_ID.to_string(), Box::new(DummySessionBinder))
        .build()
}

/// Creates a client-side `SessionConfig` using dummy verification for testing.
pub fn dummy_client_session_config() -> SessionConfig {
    SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
        .add_peer_verifier_with_binding_verifier_provider(
            DUMMY_ATTESTATION_ID.to_string(),
            Box::new(DummyVerifier),
            Box::new(DummySessionBindingVerifierProvider),
        )
        .build()
}

/// A dummy attester that returns Evidence with a known dummy certificate.
pub struct DummyAttester;

impl Attester for DummyAttester {
    fn extend(&mut self, _encoded_event: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }

    fn quote(&self) -> anyhow::Result<Evidence> {
        Ok(Evidence {
            application_keys: Some(oak_proto_rust::oak::attestation::v1::ApplicationKeys {
                encryption_public_key_certificate: DUMMY_EVIDENCE_CERTIFICATE.to_vec(),
                ..Default::default()
            }),
            ..Default::default()
        })
    }
}

/// A dummy endorser that returns default Endorsements.
pub struct DummyEndorser;

impl Endorser for DummyEndorser {
    fn endorse(&self, _evidence: Option<&Evidence>) -> anyhow::Result<Endorsements> {
        Ok(Endorsements {
            r#type: Some(Type::OakContainers(OakContainersEndorsements { ..Default::default() })),
            ..Default::default()
        })
    }
}

/// A dummy session binder that returns the data as-is.
pub struct DummySessionBinder;

impl SessionBinder for DummySessionBinder {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        bound_data.to_vec()
    }
}

/// A dummy verifier that checks for the expected dummy certificate in the
/// Evidence before returning success.
pub struct DummyVerifier;

impl AttestationVerifier for DummyVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        _endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        let cert = evidence
            .application_keys
            .as_ref()
            .map(|keys| keys.encryption_public_key_certificate.as_slice())
            .unwrap_or_default();
        anyhow::ensure!(
            cert == DUMMY_EVIDENCE_CERTIFICATE,
            "unexpected dummy certificate: expected {:?}, got {:?}",
            DUMMY_EVIDENCE_CERTIFICATE,
            cert
        );
        Ok(AttestationResults { status: Status::Success.into(), ..Default::default() })
    }
}

/// A dummy binding verifier that always succeeds.
#[derive(Debug)]
pub struct DummySessionBindingVerifier;

impl SessionBindingVerifier for DummySessionBindingVerifier {
    fn verify_binding(&self, _bound_data: &[u8], _binding: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }
}

/// A dummy provider that always creates a DummySessionBindingVerifier.
pub struct DummySessionBindingVerifierProvider;

impl SessionBindingVerifierProvider for DummySessionBindingVerifierProvider {
    fn create_session_binding_verifier(
        &self,
        _attestation_results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn SessionBindingVerifier>> {
        Ok(Box::new(DummySessionBindingVerifier))
    }
}

/// A verifier that always rejects evidence, for testing that clients abort on
/// bad attestation.
pub struct RejectingVerifier;

impl AttestationVerifier for RejectingVerifier {
    fn verify(
        &self,
        _evidence: &Evidence,
        _endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults> {
        anyhow::bail!("attestation evidence rejected: untrusted server")
    }
}
