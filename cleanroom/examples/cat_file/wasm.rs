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

use std::io::{self, Read, Write};

fn main() {
    let mut buf = Vec::new();
    io::stdin().read_to_end(&mut buf).expect("reading stdin");
    let path = String::from_utf8_lossy(&buf);
    let path = path.trim();

    if path.is_empty() {
        eprintln!("No path provided in stdin");
        std::process::exit(1);
    }

    eprintln!("Catting file: {path}");

    match cleanroom_sdk::read_file(path) {
        Ok(data) => {
            io::stdout().write_all(&data).expect("writing stdout");
        }
        Err(e) => {
            eprintln!("Failed to read file via proxy: {path}: {e}");
            std::process::exit(1);
        }
    }
}
