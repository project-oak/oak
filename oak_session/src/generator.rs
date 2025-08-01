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

use alloc::{boxed::Box, string::String};

#[cfg(test)]
use mockall::automock;
use oak_proto_rust::oak::session::v1::{Assertion, SessionBinding};
use strum::Display;
use thiserror::Error;

/// Errors that can occur during assertion verification.
#[derive(Error, Debug, Display)]
pub enum AssertionGenerationError {
    //  #[error("Generic verification error")]
    GenericFailure { error_msg: String },
    //  #[error("Generic verification error")]
    BindingVerificationFailure { error_msg: String },
}

/// Defines the behavior for generating assertions that can be cryptographically
/// bound to the established session. Instances of `AssertionGenerator` are
/// provided by the application and used by the session to obtain and send the
/// assertions to the peer during the attestation step of the session
/// initialization.
#[cfg_attr(test, automock)]
pub trait AssertionGenerator: Send + Sync {
    /// Generates an assertion to be sent to a peer during attestation. In the
    /// Oak session protocol attestation happens before a secure channel is
    /// established through a cryptographic handshake and will need to be
    /// further bound to the channel.
    fn generate(&self) -> Result<Box<dyn BindableAssertion>, AssertionGenerationError>;
}

/// Assertion that can be bound to the session
pub trait BindableAssertion: Send + Sync {
    /// Returns the underlying assertion to be included in the verification.
    fn assertion(&self) -> &Assertion;

    /// Binds the assertion to the session handshake and other metadata. Binding
    /// happens after the attestation and the handshake is complete and
    /// generates a proof that the attestation and the handshake match each
    /// other. The binding mechanism is specific to the assertion, the designer
    /// of an attestation type can choose the one that best suits their use
    /// case.
    ///
    /// One typical approach involves signing the `bound_data` (which includes
    /// the handshake hash and a hash of exchanged attestation messages)
    /// using an assertion-specific binding key.The corresponding
    /// `AssertionVerifier` will receive the same `bound_data` when
    /// verifying the binding and is expected to pass if the assertion
    /// contains the same binding key.
    fn bind(&self, bound_data: &[u8]) -> Result<SessionBinding, AssertionGenerationError>;
}
