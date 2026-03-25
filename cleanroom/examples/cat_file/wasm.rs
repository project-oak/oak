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

use std::io::{self, Read};

fn main() -> io::Result<()> {
    let mut buf = String::new();
    io::stdin().read_to_string(&mut buf)?;
    let path = buf.trim();

    if path.is_empty() {
        eprintln!("No path provided in stdin");
        std::process::exit(1);
    }

    eprintln!("Catting file: {}", path);

    let data = cleanroom_sdk::read_file(path).map_err(|e| {
        eprintln!("Failed to read file via custom ABI {}: {}", path, e);
        std::io::Error::new(std::io::ErrorKind::Other, e)
    })?;

    let contents = String::from_utf8(data).map_err(|e| {
        eprintln!("Failed to parse file contents as UTF-8: {}", e);
        std::io::Error::new(std::io::ErrorKind::InvalidData, e)
    })?;

    print!("{}", contents);

    Ok(())
}
