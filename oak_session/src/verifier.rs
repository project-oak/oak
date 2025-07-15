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
use alloc::{boxed::Box, string::String};
use core::fmt::Debug;

#[cfg(test)]
use mockall::automock;
use oak_proto_rust::oak::session::v1::{Assertion, SessionBinding};
use strum::Display;
use thiserror::Error;

/// Errors that can occur during assertion verification.
#[derive(Clone, Error, Debug, Display)]
pub enum AssertionVerificationError {
    //  #[error("Generic verification error")]
    GenericFailure { error_msg: String },
    //  #[error("Generic verification error")]
    BindingVerificationFailure { error_msg: String },
    //  #[error("Peer assertion missing")]
    PeerAssertionMissing,
}

/// Represents an assertion that has been successfully verified.
///
/// This trait provides a common interface for interacting with verified
/// assertions, allowing access to the original assertion data and enabling
/// further verification steps, namely, session binding.
pub trait VerifiedAssertion: Send + Sync + Debug {
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
    ) -> Result<(), AssertionVerificationError>;
}

/// Represents the outcome of an assertion verification attempt. In addition to
/// the `Success` and `Failure`` states that can be represented by the `Result`
/// enum it includes `Missing` and `Unverified` cases which can be treated
/// differently by the results aggregator.
#[derive(Debug)]
pub enum AssertionVerifierResult {
    /// Verifier yielded a success result.
    ///
    /// Contains the original `Assertion`` and its extracted `Payload``.
    Success { verified_assertion: Box<dyn VerifiedAssertion> },
    /// Verifier returned a failure.
    ///
    /// Contains the original `Assertion` and the `VerificationError` detailing
    /// the reason for the failure.
    Failure { assertion: Assertion, error: AssertionVerificationError },
    /// No assertion has been supplied for the verifier.
    Missing,
    /// The assertion has been presented but no verifier is configured.
    ///
    /// Contains the original `Assertion` that could not be verified due to
    /// a missing configuration.
    Unverified { assertion: Assertion },
}

/// Defines the behavior for verifying assertions and their session bindings.
/// Instances of `AssertionVerifier` are provided by the API client and used by
/// the session to determine the outcome of the attestation step and to verify
/// the session binding after the handshake.
///
/// Implementors of this trait are responsible for validating the authenticity
/// and integrity of received [`Assertion`]s, extracting any relevant payload,
/// and then verifying that the assertion is correctly bound to the session.
#[cfg_attr(test, automock)]
pub trait AssertionVerifier: Send + Sync {
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
    ) -> Result<Box<dyn VerifiedAssertion>, AssertionVerificationError>;
}
