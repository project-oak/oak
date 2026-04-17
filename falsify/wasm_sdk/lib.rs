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

//! SDK for building falsification claims as WebAssembly modules.
//!
//! This crate provides the glue between a [`Claim`] implementation and the
//! Wasm host runner. It reuses [`oak_functions_sdk`] for low-level Wasm I/O
//! (the `invoke` ABI, `alloc`, `read_request`, `write_response`), since the
//! host runner uses `OakFunctionsInstance` from [`oak_functions_service`].
//!
//! # Usage
//!
//! ```ignore
//! struct MyClaim;
//! impl falsify_wasm_sdk::Claim for MyClaim {
//!     fn evaluate(&self, input: &[u8])
//!         -> Result<falsify_wasm_sdk::Evaluation, Box<dyn core::error::Error>> {
//!         // ...
//!         Ok(falsify_wasm_sdk::Evaluation::Intact)
//!     }
//! }
//!
//! #[unsafe(no_mangle)]
//! pub extern "C" fn main() {
//!     falsify_wasm_sdk::run(&MyClaim);
//! }
//! ```

#![no_std]

// Re-export the shared types so claim authors only need one dep.
pub use falsify::{Claim, Evaluation};

/// Runs a claim against the input provided by the host.
///
/// 1. Reads the input payload via [`oak_functions_sdk::read_request`].
/// 2. Calls `claim.evaluate(&input)`.
/// 3. Writes the evaluation result via [`oak_functions_sdk::write_response`].
///
/// The response is a single byte encoding the evaluation result:
/// - `0x00`: [`Evaluation::Intact`] — the claim held for this input.
/// - `0x01`: [`Evaluation::Falsified`] — the input falsified the claim.
///
/// If the claim returns an `Err` or panics, the function traps, which the host
/// runner interprets as an error (inconclusive result).
pub fn run(claim: &dyn Claim) {
    let input = oak_functions_sdk::read_request().expect("failed to read request from host");

    let evaluation = match claim.evaluate(&input) {
        Ok(eval) => eval,
        Err(e) => panic!("Claim error: {e}"),
    };

    let response = [evaluation.to_byte()];

    oak_functions_sdk::write_response(&response).expect("failed to write response to host");
}
