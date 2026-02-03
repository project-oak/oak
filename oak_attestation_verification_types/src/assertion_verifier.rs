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

use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
};

use oak_proto_rust::oak::attestation::v1::{Assertion, WrapperAssertion};
use oak_time::Instant;
use prost::{DecodeError, Message};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum AssertionVerifierError {
    #[error(
        "Data in the assertion doesn't match the expected asserted data. Expected: {expected}, actual: {actual}"
    )]
    AssertedDataMismatch { expected: String, actual: String },
    #[error("Assertion parsing error: {0:?}")]
    AssertionParsingError(DecodeError),
    #[error("Assertion missing expected fields: {error_msg}")]
    AssertionMissingExpectedFields { error_msg: String },
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

// Needs to be explicitly defined because we can't use the #[from] macro. Due to
// our patching prost is std at compile time, and so DecodeError ends up being
// incompatible with the std version of thiserror.
impl From<DecodeError> for AssertionVerifierError {
    fn from(value: DecodeError) -> Self {
        Self::AssertionParsingError(value)
    }
}

/// Trait that provides the functionality for checking that the assertion is
/// valid for the given data.
#[cfg_attr(test, automock)]
pub trait AssertionVerifier: Send + Sync {
    /// Checks that an assertion is valid for the data at the specified time
    /// instant.
    fn verify(
        &self,
        assertion: &Assertion,
        asserted_data: &[u8],
        verification_time: Instant,
    ) -> Result<(), AssertionVerifierError>;
}

/// A trait for building an AssertionVerifier.
///
/// **Dynamically creates** an 'outer' `AssertionVerifier` whose configuration
/// (e.g., a required public key or policy ID) **depends directly on the
/// verified data** (`asserted_data`) from a preceding, 'inner' verification
/// step.
///
/// This is used to ensure the outer verification mechanism of
/// `WrapperAssertion` is itself *asserted* by the inner assertion.
pub trait AssertionVerifierBuilder: Send + Sync {
    fn build(&self, asserted_data: &[u8]) -> Box<dyn AssertionVerifier>;
}

pub struct WrapperAssertionVerifier {
    inner_assertion_verifier: Arc<dyn AssertionVerifier>,
    outer_assertion_verifier_builder: Arc<dyn AssertionVerifierBuilder>,
}

impl AssertionVerifier for WrapperAssertionVerifier {
    fn verify(
        &self,
        assertion: &Assertion,
        asserted_data: &[u8],
        verification_time: Instant,
    ) -> Result<(), AssertionVerifierError> {
        let wrapper_assertion = WrapperAssertion::decode(assertion.content.as_slice())?;
        self.inner_assertion_verifier.verify(
            &wrapper_assertion.inner_assertion.ok_or(
                AssertionVerifierError::AssertionMissingExpectedFields {
                    error_msg: "missing inner_assertion".to_string(),
                },
            )?,
            wrapper_assertion.inner_asserted_data.as_slice(),
            verification_time,
        )?;
        let outer_assertion_verifier = self
            .outer_assertion_verifier_builder
            .build(wrapper_assertion.inner_asserted_data.as_slice());
        outer_assertion_verifier.verify(
            &wrapper_assertion.outer_assertion.ok_or(
                AssertionVerifierError::AssertionMissingExpectedFields {
                    error_msg: "missing outer_assertion".to_string(),
                },
            )?,
            asserted_data,
            verification_time,
        )
    }
}
