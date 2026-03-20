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

//! Cleanroom example: count lines, words, and bytes in the input (like `wc`).
//!
//! Outputs a single line: `{lines} {words} {bytes}\n`
//!
//! Run via cleanroom:
//! ```text
//! echo "hello world" | cleanroom --wasm-module-file=word_count.wasm
//! # → 1 2 12
//! ```

#[unsafe(no_mangle)]
pub extern "C" fn main() {
    cleanroom_sdk::run_with(|input: &[u8]| -> Vec<u8> {
        let bytes = input.len();
        let lines = input.iter().filter(|&&b| b == b'\n').count();
        let words = input.split(|b| b.is_ascii_whitespace()).filter(|s| !s.is_empty()).count();
        format!("{lines} {words} {bytes}\n").into_bytes()
    });
}
