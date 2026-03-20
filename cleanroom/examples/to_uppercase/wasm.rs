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

//! Cleanroom example: convert all ASCII letters in the input to uppercase.
//!
//! Run via cleanroom:
//! ```text
//! echo "hello world" | cleanroom --wasm-module-file=to_uppercase.wasm
//! # → HELLO WORLD
//! ```

#[unsafe(no_mangle)]
pub extern "C" fn main() {
    cleanroom_sdk::run_with(|input: &[u8]| -> Vec<u8> {
        input.iter().map(|b| b.to_ascii_uppercase()).collect()
    });
}
