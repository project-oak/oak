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

use clap::Parser;

/// Predicate for the Unattested Noise Protocol NN Handshake Encryption and
/// Decryption test.
///
/// Ensures that encryption and decryption flows behave deterministically and do
/// not panic when supplied with valid or invalid inputs.
struct NnPredicate;

impl falsify::Claim for NnPredicate {
    fn evaluate(&self, input: &[u8]) -> Result<falsify::Evaluation, Box<dyn core::error::Error>> {
        oak_session_testing::test_unattested_nn_encryption_and_decryption_inner(input.to_vec())?;
        Ok(falsify::Evaluation::Intact)
    }
}

fn main() {
    falsify_native::falsify(falsify_native::FalsifyArgs::parse(), &NnPredicate);
}
