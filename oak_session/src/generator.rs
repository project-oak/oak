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

use alloc::{boxed::Box, format, string::String, sync::Arc};

use oak_attestation_types::assertion_generator::{AssertionGenerator, AssertionGeneratorError};
use oak_proto_rust::oak::{
    attestation::v1::Assertion,
    session::v1::{SessionBinding, SessionBindingKeyWrapperAssertion},
};
use p256::ecdsa::{signature::Signer, Signature, SigningKey};
use prost::Message;
use thiserror::Error;

/// Errors that can occur during assertion verification.
#[derive(Error, Debug)]
pub enum BindableAssertionGeneratorError {
    #[error("Generic assertion generation error")]
    GenericFailure { error_msg: String },
    #[error("Assertion binding failure")]
    BindingGenerationFailure { error_msg: String },
    #[error(transparent)]
    AssertionGenerationFailure(#[from] AssertionGeneratorError),
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

/// Defines the behavior for generating assertions that can be cryptographically
/// bound to the established session. Instances of `BindableAssertionGenerator`
/// are provided by the application and used by the session to obtain and send
/// the assertions to the peer during the attestation step of the session
/// initialization.
pub trait BindableAssertionGenerator: Send + Sync {
    /// Generates an assertion to be sent to a peer during attestation. In the
    /// Oak session protocol attestation happens before a secure channel is
    /// established through a cryptographic handshake and will need to be
    /// further bound to the channel.
    fn generate(&self) -> Result<Box<dyn BindableAssertion>, BindableAssertionGeneratorError>;
}

/// Assertion that can be bound to the session
pub trait BindableAssertion: Send + Sync {
    /// Returns the underlying assertion to be sent to the peer. The assumption
    /// is that the assertion includes enough information for the peer to verify
    /// the binding (e.g., a public binding key).
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
    /// `BoundAssertionVerifier` will receive the same `bound_data` when
    /// verifying the binding and is expected to pass if the assertion
    /// contains the same binding key.
    fn bind(&self, bound_data: &[u8]) -> Result<SessionBinding, BindableAssertionGeneratorError>;
}

/// An implementation of [`BindableAssertion`] that uses a [`Signer`] to
/// generate a signature over the bound data.
struct SessionKeyBindableAssertion {
    assertion: Assertion,
    binding_signer: Arc<SigningKey>,
}

impl BindableAssertion for SessionKeyBindableAssertion {
    fn assertion(&self) -> &Assertion {
        &self.assertion
    }

    fn bind(&self, bound_data: &[u8]) -> Result<SessionBinding, BindableAssertionGeneratorError> {
        let signature: Signature = self.binding_signer.try_sign(bound_data).map_err(|err| {
            BindableAssertionGeneratorError::BindingGenerationFailure {
                error_msg: format!("failed to sign bound data: {:?}", err),
            }
        })?;
        Ok(SessionBinding { binding: signature.to_vec() })
    }
}

/// An implementation of [`BindableAssertionGenerator`] that uses a dynamic
/// [`AssertionGenerator`] to generate an assertion about the public key of a
/// [`Signer`] that is used for binding the assertion.
pub struct SessionKeyBindableAssertionGenerator {
    session_key_assertion: Assertion,
    binding_signer: Arc<SigningKey>,
}

impl SessionKeyBindableAssertionGenerator {
    pub fn create_with_assertion_generator(
        assertion_generator: &dyn AssertionGenerator,
        binding_signer: Arc<SigningKey>,
    ) -> Result<Self, AssertionGeneratorError> {
        let public_key = binding_signer.verifying_key().to_sec1_bytes();
        let inner_assertion = assertion_generator.generate(&public_key)?;
        Ok(Self::create_with_assertion(inner_assertion, binding_signer))
    }

    pub fn create_with_assertion(
        inner_assertion: Assertion,
        binding_signer: Arc<SigningKey>,
    ) -> Self {
        let public_key = binding_signer.verifying_key().to_sec1_bytes();
        let binding_key_assertion = SessionBindingKeyWrapperAssertion {
            public_binding_key: public_key.to_vec(),
            inner_assertion: Some(inner_assertion),
        };
        let session_key_assertion = Assertion { content: binding_key_assertion.encode_to_vec() };
        Self { session_key_assertion, binding_signer }
    }
}

impl BindableAssertionGenerator for SessionKeyBindableAssertionGenerator {
    fn generate(&self) -> Result<Box<dyn BindableAssertion>, BindableAssertionGeneratorError> {
        let bindable_assertion = SessionKeyBindableAssertion {
            assertion: self.session_key_assertion.clone(),
            binding_signer: self.binding_signer.clone(),
        };

        Ok(Box::new(bindable_assertion))
    }
}
