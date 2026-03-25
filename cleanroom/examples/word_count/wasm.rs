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
//! Uses standard Rust `std::io` and WASI.

use std::io::{Read, Write};

fn main() {
    let mut buf = Vec::new();
    if std::io::stdin().read_to_end(&mut buf).is_ok() {
        let bytes = buf.len();
        let lines = buf.iter().filter(|&&b| b == b'\n').count();
        let words = buf.split(|b| b.is_ascii_whitespace()).filter(|s| !s.is_empty()).count();
        let out = format!("{lines} {words} {bytes}\n");
        let _ = std::io::stdout().write_all(out.as_bytes());
    }
}
