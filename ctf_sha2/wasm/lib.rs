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

//! Wasm-compiled version of the CTF SHA-2 arbiter claim.
//!
//! This is a thin wrapper that calls `falsify_wasm_sdk::run()` with the
//! `Arbiter` claim, which is compiled into a Wasm module for execution by the
//! `falsify_wasm` runner.

// The Arbiter claim implementation lives in the parent crate.
use ctf_sha2::Arbiter;

#[unsafe(no_mangle)]
pub extern "C" fn main() {
    falsify_wasm_sdk::run(&Arbiter);
}
