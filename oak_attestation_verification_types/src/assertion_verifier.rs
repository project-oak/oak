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

use alloc::vec::Vec;

use oak_proto_rust::oak::attestation::v1::Assertion;
use oak_time::Instant;
use strum::Display;
use thiserror::Error;

#[derive(Debug, Display, Error)]
pub enum AssertionVerifierError {
    //  #[error("Data in the assertion doesn't match the expected asserted data. Expected:
    // {expected}, actual: {actual}")]
    AssertedDataMismatch { expected: Vec<u8>, actual: Vec<u8> },
    // #[error(transparent)]
    Other(#[from] anyhow::Error),
}

/// Trait that provides the functionality for checking that the assertion is
/// valid for the given data
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
