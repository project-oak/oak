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
use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    sync::Arc,
};
use core::fmt::Debug;

use oak_attestation_verification_types::assertion_verifier::AssertionVerifier;
use oak_proto_rust::oak::{
    attestation::v1::Assertion,
    session::v1::{SessionBinding, SessionBindingKeyWrapperAssertion},
};
use oak_time::Clock;
use p256::ecdsa::{Signature, VerifyingKey, signature::Verifier};
use prost::{DecodeError, Message};
use thiserror::Error;

/// Errors that can occur during assertion verification.
#[derive(Clone, Error, Debug)]
pub enum BoundAssertionVerificationError {
    #[error("Generic verification error: {error_msg}")]
    GenericFailure { error_msg: String },
    #[error("Binding verification error: {error_msg}")]
    BindingVerificationFailure { error_msg: String },
    #[error("Peer assertion missing")]
    PeerAssertionMissing,
    #[error("Assertion parsing error: {0:?}")]
    AssertionParsingError(DecodeError),
    #[error("Assertion missing expected fields: {error_msg}")]
    AssertionMissingExpectedFields { error_msg: String },
}

// Needs to be explicitly defined because we can't use the #[from] macro. Due to
// our patching prost is std at compile time, and so DecodeError ends up being
// incompatible with the std version of thiserror.
impl From<DecodeError> for BoundAssertionVerificationError {
    fn from(value: DecodeError) -> Self {
        Self::AssertionParsingError(value)
    }
}

/// Represents an assertion that has been successfully verified.
///
/// This trait provides a common interface for interacting with verified
/// assertions, allowing access to the original assertion data and enabling
/// further verification steps, namely, session binding.
///
/// The assumption  is that the underlying assertion includes enough information
/// to verify the binding (e.g., a public binding key).
pub trait VerifiedBoundAssertion: Send + Sync + Debug {
    fn assertion(&self) -> &Assertion;

    /// Verifies the session binding associated with an assertion,
    /// provided that the attestation is successsful. The binding happens after
    /// the handshake and uses the data derived from the hadnshake and the
    /// attestation steps to cryptographically prove that the assertion comes
    /// from the same party the estabished the session via the handshake.
    ///
    /// This method uses the extracted payload (e.g., binding key) to validate
    /// the `binding` against the `bound_data` (which includes session
    /// handshake hash and attestation message hash).
    fn verify_binding(
        &self,
        bound_data: &[u8],
        binding: &SessionBinding,
    ) -> Result<(), BoundAssertionVerificationError>;
}

/// Represents the outcome of an assertion verification attempt. In addition to
/// the `Success` and `Failure`` states that can be represented by the `Result`
/// enum it includes `Missing` and `Unverified` cases which can be treated
/// differently by the results aggregator.
#[derive(Debug)]
pub enum BoundAssertionVerifierResult {
    /// Verifier yielded a success result.
    ///
    /// Contains the original `Assertion`` and its extracted `Payload``.
    Success { verified_bound_assertion: Box<dyn VerifiedBoundAssertion> },
    /// Verifier returned a failure.
    ///
    /// Contains the original `Assertion` and the `VerificationError` detailing
    /// the reason for the failure.
    Failure { assertion: Assertion, error: BoundAssertionVerificationError },
    /// No assertion has been supplied for the verifier.
    Missing,
    /// The assertion has been presented but no verifier is configured.
    ///
    /// Contains the original `Assertion` that could not be verified due to
    /// a missing configuration.
    Unverified { assertion: Assertion },
}

/// Defines the behavior for verifying assertions and their session bindings.
/// Instances of `BoundAssertionVerifier` are provided by the API client and
/// used by the session to determine the outcome of the attestation step and to
/// verify the session binding after the handshake.
///
/// Implementors of this trait are responsible for validating the authenticity
/// and integrity of received [`Assertion`]s, extracting any relevant payload,
/// and then verifying that the assertion is correctly bound to the session.
pub trait BoundAssertionVerifier: Send + Sync {
    /// Verifies the provided assertion.
    ///
    /// This method checks the validity of the `assertion` based on its type
    /// and content. Successful attestation is a precondition to passing to the
    /// handshake step, otherwise the session is aborted. Upon successful
    /// verification, it returns any payload extracted from the assertion, such
    /// as a binding key. If verification fails, a `VerificationError` is
    /// returned.
    fn verify_assertion(
        &self,
        assertion: &Assertion,
    ) -> Result<Box<dyn VerifiedBoundAssertion>, BoundAssertionVerificationError>;
}

/// An implementation of [`VerifiedBoundAssertion`] that uses a [`VerifyingKey`]
/// to verify the signature over the bound data.
#[derive(Debug)]
struct SessionKeyVerifiedBoundAssertion {
    assertion: Assertion,
    binding_verifying_key: VerifyingKey,
}

impl VerifiedBoundAssertion for SessionKeyVerifiedBoundAssertion {
    fn assertion(&self) -> &Assertion {
        &self.assertion
    }

    fn verify_binding(
        &self,
        bound_data: &[u8],
        binding: &SessionBinding,
    ) -> Result<(), BoundAssertionVerificationError> {
        let signature = Signature::from_slice(&binding.binding).map_err(|err| {
            BoundAssertionVerificationError::BindingVerificationFailure {
                error_msg: format!("session binding is not a valid signature: {:?}", err),
            }
        })?;

        self.binding_verifying_key.verify(bound_data, &signature).map_err(|err| {
            BoundAssertionVerificationError::BindingVerificationFailure {
                error_msg: format!("failed to verify session binding signature: {:?}", err),
            }
        })
    }
}

/// An implementation of [`BoundAssertionVerifier`] that uses a dynamic
/// [`AssertionVerifier`] to verify an assertion about a public key that is used
/// for verifying the assertion binding.
pub struct SessionKeyBoundAssertionVerifier {
    pub assertion_verifier: Arc<dyn AssertionVerifier>,
    pub clock: Arc<dyn Clock>,
}

impl BoundAssertionVerifier for SessionKeyBoundAssertionVerifier {
    fn verify_assertion(
        &self,
        assertion: &Assertion,
    ) -> Result<Box<dyn VerifiedBoundAssertion>, BoundAssertionVerificationError> {
        let binding_key_assertion =
            SessionBindingKeyWrapperAssertion::decode(assertion.content.as_slice())?;
        let public_key = binding_key_assertion.public_binding_key.as_slice();
        self.assertion_verifier
            .verify(
                &binding_key_assertion.inner_assertion.ok_or(
                    BoundAssertionVerificationError::AssertionMissingExpectedFields {
                        error_msg: "missing inner_assertion in SessionBindingKeyWrapperAssertion"
                            .to_string(),
                    },
                )?,
                public_key,
                self.clock.get_time(),
            )
            .map_err(|err| BoundAssertionVerificationError::GenericFailure {
                error_msg: format!("failed to verify assertion: {:?}", err),
            })?;

        let binding_verifying_key = VerifyingKey::from_sec1_bytes(public_key).map_err(|err| {
            BoundAssertionVerificationError::GenericFailure {
                error_msg: format!("failed to create verifier from public key: {:?}", err),
            }
        })?;

        let verified_assertion = SessionKeyVerifiedBoundAssertion {
            assertion: assertion.clone(),
            binding_verifying_key,
        };

        Ok(Box::new(verified_assertion))
    }
}
