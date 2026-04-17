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

use std::io::{self, Read};

fn main() {
    let mut buf = Vec::new();
    io::stdin().read_to_end(&mut buf).expect("reading stdin");
    let bytes = buf.len();
    let lines = buf.iter().filter(|&&b| b == b'\n').count();
    let words = buf.split(|b| b.is_ascii_whitespace()).filter(|s| !s.is_empty()).count();
    println!("{lines} {words} {bytes}");
}
