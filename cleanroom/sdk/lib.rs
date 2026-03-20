// Copyright 2026 The Project Oak Authors
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

//! # Cleanroom SDK
//!
//! Helpers for writing WebAssembly modules that run inside the
//! [cleanroom](../README.md) sandboxed runner.
//!
//! Cleanroom modules use the [Oak Functions ABI] — the same ABI used by Oak
//! Functions and Oak Verity. This crate is a thin wrapper around
//! [`oak_functions_sdk`] that adds a convenient [`run_with`] helper so module
//! authors don't need to call `read_request` / `write_response` manually.
//!
//! ## Usage
//!
//! ```ignore
//! #![no_std]
//! extern crate alloc;
//! use alloc::vec::Vec;
//!
//! #[unsafe(no_mangle)]
//! pub extern "C" fn main() {
//!     cleanroom_sdk::run_with(|input| {
//!         input.iter().map(|b| b.to_ascii_uppercase()).collect()
//!     });
//! }
//! ```
//!
//! The `alloc` export required by the Oak Functions ABI is provided
//! automatically by `oak_functions_sdk`, so you do not need to supply it.
//!
//! [Oak Functions ABI]: https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

// Re-export the low-level primitives so module authors can use them directly
// if they need finer-grained control.
pub use oak_functions_sdk::{read_request, write_response};

/// Reads all input bytes from the host (stdin), applies `f` to them,
/// and writes the resulting bytes back to the host (stdout).
///
/// This is the primary entry point for cleanroom modules. Call it inside
/// the exported `main` function:
///
/// ```ignore
/// #[unsafe(no_mangle)]
/// pub extern "C" fn main() {
///     cleanroom_sdk::run_with(|input| {
///         input.iter().copied().rev().collect()
///     });
/// }
/// ```
///
/// # Panics
///
/// Panics (causing a Wasm trap) if reading from the host or writing to the
/// host fails. This is the correct behaviour: a trap is surfaced as an error
/// by the cleanroom runner and printed to stderr.
pub fn run_with<F>(f: F)
where
    F: FnOnce(&[u8]) -> Vec<u8>,
{
    let input = read_request().expect("cleanroom_sdk: failed to read request from host");
    let output = f(&input);
    write_response(&output).expect("cleanroom_sdk: failed to write response to host");
}
