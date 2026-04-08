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
//! Uses standard WASI I/O. IFC enforcement is handled automatically by
//! the cleanroom runtime at module boundary.

use std::io::{self, Read, Write};

fn main() {
    let mut buf = Vec::new();
    io::stdin().read_to_end(&mut buf).expect("reading stdin");
    let out: Vec<u8> = buf.iter().map(|b| b.to_ascii_uppercase()).collect();
    io::stdout().write_all(&out).expect("writing stdout");
}
