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

use alloc::{sync::Arc, vec::Vec};

use oak_proto_rust::oak::attestation::v1::{Assertion, WrapperAssertion};
use prost::Message;
use thiserror::Error;

#[derive(Debug, Error)]
#[error("AssertionGenerator error: {from:?}")]
pub struct AssertionGeneratorError {
    #[from]
    pub from: anyhow::Error,
}

/// Trait that provides the functionality for generating an assertion for the
/// supplied data.
#[cfg_attr(test, automock)]
pub trait AssertionGenerator: Send + Sync {
    /// Produces an assertion for the provided data.
    fn generate(&self, data: &[u8]) -> Result<Assertion, AssertionGeneratorError>;
}

/// A generator capable of exporting the data that can be used to bootstrap its
/// verification counterpart. The data can be asserted by another
/// [`AssertionGenerator`] effectively creating a chain of assertions.
///
/// Implementors of this trait guarantee that the binary data returned by
/// `export_verifier_data` is sufficient to construct a valid
/// [`AssertionVerifier`] capable of validating the assertions produced by
/// `self`.
pub trait ChainableAssertionGenerator: AssertionGenerator {
    /// Exports the binary data (e.g. public key) needed to build a matching
    /// [`AssertionVerifier`].
    fn export_verifier_data(&self) -> Result<Vec<u8>, AssertionGeneratorError>;
}

/// Assertion generator that produces [`WrapperAssertion`]s chaining two
/// assertion generators together.
pub struct WrapperAssertionGenerator {
    inner_assertion: Assertion,
    inner_asserted_data: Vec<u8>,
    outer_assertion_generator: Arc<dyn AssertionGenerator>,
}

impl WrapperAssertionGenerator {
    pub fn create(
        inner_assertion_generator: Arc<dyn AssertionGenerator>,
        outer_assertion_generator: Arc<dyn ChainableAssertionGenerator>,
    ) -> Result<Self, AssertionGeneratorError> {
        let inner_asserted_data = outer_assertion_generator.export_verifier_data()?;
        Ok(Self {
            inner_assertion: inner_assertion_generator.generate(inner_asserted_data.as_slice())?,
            inner_asserted_data,
            outer_assertion_generator,
        })
    }
}

impl AssertionGenerator for WrapperAssertionGenerator {
    fn generate(&self, data: &[u8]) -> Result<Assertion, AssertionGeneratorError> {
        let wrapper_assertion = WrapperAssertion {
            inner_assertion: Some(self.inner_assertion.clone()),
            inner_asserted_data: self.inner_asserted_data.clone(),
            outer_assertion: Some(self.outer_assertion_generator.generate(data)?),
        };
        Ok(Assertion { content: wrapper_assertion.encode_to_vec() })
    }
}
