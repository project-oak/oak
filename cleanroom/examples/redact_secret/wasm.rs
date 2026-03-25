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

use std::io;

fn main() -> io::Result<()> {
    // Read "secret_api_key" from the cell store (taints computation
    // with {secret_category}).
    let input = cleanroom_sdk::get_cell("secret_api_key").ok_or_else(|| {
        io::Error::new(io::ErrorKind::Other, "Could not read secret_api_key from cell")
    })?;

    // Simulate redaction: preserve first 4 characters, redact rest.
    let redacted = if input.len() > 4 {
        format!("{}{}", &input[..4], "*".repeat(input.len() - 4))
    } else {
        "****".to_string()
    };

    // The raw secret has been redacted — declassify so the output can
    // be released.
    cleanroom_sdk::declassify(&["secret_category"]);

    println!("Redacted secret: {}", redacted);

    Ok(())
}
