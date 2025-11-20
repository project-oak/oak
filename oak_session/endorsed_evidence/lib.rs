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

#![no_std]

#[macro_use]
extern crate alloc;

use alloc::{boxed::Box, string::ToString, sync::Arc};

use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_proto_rust::oak::{
    attestation::v1::{attestation_results::Status, Assertion},
    session::v1::{EndorsedEvidence, SessionBinding},
};
use oak_session::{
    generator::{BindableAssertion, BindableAssertionGenerator, BindableAssertionGeneratorError},
    session_binding::{SessionBinder, SessionBindingVerifier, SessionBindingVerifierProvider},
    verifier::{BoundAssertionVerificationError, BoundAssertionVerifier, VerifiedBoundAssertion},
};
use prost::Message;

/// An implementation of [`BindableAssertion`] that contains
/// [`EndorsedEvidence`] and is bound to the session using the supplied
/// [`SessionBinder`].
struct EndorsedEvidenceBindableAssertion {
    assertion: Assertion,
    session_binder: Arc<dyn SessionBinder>,
}

impl BindableAssertion for EndorsedEvidenceBindableAssertion {
    fn assertion(&self) -> &Assertion {
        &self.assertion
    }

    fn bind(&self, bound_data: &[u8]) -> Result<SessionBinding, BindableAssertionGeneratorError> {
        Ok(SessionBinding { binding: self.session_binder.bind(bound_data) })
    }
}

/// An implementation of [`BindableAssertionGenerator`] that uses an
/// [`Attester`] to generate evidence and an [`Endorser`] to endorse it. The
/// resulting assertion contains serialized [`EndorsedEvidence`], and the
/// session bindings for it are created by the supplied [`SessionBinder`].
pub struct EndorsedEvidenceBindableAssertionGenerator {
    attester: Arc<dyn Attester>,
    endorser: Arc<dyn Endorser>,
    session_binder: Arc<dyn SessionBinder>,
}

impl EndorsedEvidenceBindableAssertionGenerator {
    pub fn new(
        attester: Arc<dyn Attester>,
        endorser: Arc<dyn Endorser>,
        session_binder: Arc<dyn SessionBinder>,
    ) -> Self {
        Self { attester, endorser, session_binder }
    }
}

impl BindableAssertionGenerator for EndorsedEvidenceBindableAssertionGenerator {
    fn generate(&self) -> Result<Box<dyn BindableAssertion>, BindableAssertionGeneratorError> {
        let evidence = self.attester.quote()?;
        let endorsed_evidence = EndorsedEvidence {
            endorsements: Some(self.endorser.endorse(Some(&evidence))?),
            evidence: Some(evidence),
        };
        let assertion = Assertion { content: endorsed_evidence.encode_to_vec() };
        Ok(Box::new(EndorsedEvidenceBindableAssertion {
            assertion,
            session_binder: self.session_binder.clone(),
        }))
    }
}

/// An implementation of [`VerifiedBoundAssertion`] that contains
/// [`EndorsedEvidence`] from a peer and can verify that it is properly bound to
/// the session using the provided [`SessionBindingVerifier`].
#[derive(Debug)]
struct EndorsedEvidenceBoundAssertion {
    assertion: Assertion,
    binding_verifier: Box<dyn SessionBindingVerifier>,
}

impl VerifiedBoundAssertion for EndorsedEvidenceBoundAssertion {
    fn assertion(&self) -> &Assertion {
        &self.assertion
    }

    fn verify_binding(
        &self,
        bound_data: &[u8],
        binding: &SessionBinding,
    ) -> Result<(), BoundAssertionVerificationError> {
        self.binding_verifier.verify_binding(bound_data, &binding.binding).map_err(|e| {
            BoundAssertionVerificationError::BindingVerificationFailure {
                error_msg: format!("{e:#}"),
            }
        })
    }
}

/// An implementation of [`BoundAssertionVerifier`] that uses an
/// [`AttestationVerifier`] to verify [`EndorsedEvidence`]. Session bindings are
/// verified by a [`SessionBindingVerifier`] created by the supplied
/// [`SessionBindingVerifierProvider`] from the [`AttestationResults`] obtained
/// during verification.
pub struct EndorsedEvidenceBoundAssertionVerifier {
    attestation_verifier: Arc<dyn AttestationVerifier>,
    session_binding_verifier_provider: Arc<dyn SessionBindingVerifierProvider>,
}

impl EndorsedEvidenceBoundAssertionVerifier {
    pub fn new(
        attestation_verifier: Arc<dyn AttestationVerifier>,
        session_binding_verifier_provider: Arc<dyn SessionBindingVerifierProvider>,
    ) -> Self {
        Self { attestation_verifier, session_binding_verifier_provider }
    }
}

impl BoundAssertionVerifier for EndorsedEvidenceBoundAssertionVerifier {
    fn verify_assertion(
        &self,
        assertion: &Assertion,
    ) -> Result<Box<dyn VerifiedBoundAssertion>, BoundAssertionVerificationError> {
        let endorsed_evidence = EndorsedEvidence::decode(assertion.content.as_slice())?;
        let attestation_results = self
            .attestation_verifier
            .verify(
                &endorsed_evidence.evidence.ok_or(
                    BoundAssertionVerificationError::AssertionMissingExpectedFields {
                        error_msg: "no evidence in the endorsed evidence".to_string(),
                    },
                )?,
                &endorsed_evidence.endorsements.ok_or(
                    BoundAssertionVerificationError::AssertionMissingExpectedFields {
                        error_msg: "no endorsements in the endorsed evidence".to_string(),
                    },
                )?,
            )
            .map_err(|e| BoundAssertionVerificationError::GenericFailure {
                error_msg: format!("verification failed: {e:#?}"),
            })?;
        match attestation_results.status.try_into().map_err(|_| {
            BoundAssertionVerificationError::GenericFailure {
                error_msg: format!(
                    "unknown status in the attestation results: {}",
                    attestation_results.status
                ),
            }
        })? {
            Status::Success => Ok(Box::new(EndorsedEvidenceBoundAssertion {
                assertion: assertion.clone(),
                binding_verifier: self
                    .session_binding_verifier_provider
                    .create_session_binding_verifier(&attestation_results)
                    .map_err(|e| BoundAssertionVerificationError::GenericFailure {
                        error_msg: format!("failed to create a session binding verifier: {e:#?}"),
                    })?,
            })),
            Status::GenericFailure => Err(BoundAssertionVerificationError::GenericFailure {
                error_msg: format!("legacy verification failed: {}", attestation_results.reason),
            }),
            Status::Unspecified => Err(BoundAssertionVerificationError::GenericFailure {
                error_msg: "legacy verification failed with unspecified status".to_string(),
            }),
        }
    }
}
