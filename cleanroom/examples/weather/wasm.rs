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

/// Fetches weather from wttr.in.
///
/// Reads a city name from the `user_location` cell, fetches weather
/// data for that city, and prints the result.  IFC enforcement is
/// handled by the runtime automatically.
fn main() -> io::Result<()> {
    // 1. Read the labeled data from the cell store.
    let city = match cleanroom_sdk::read_cell("user_location") {
        Some(val) => val,
        None => {
            // Fall back to reading from stdin.
            let mut buf = Vec::new();
            io::stdin().read_to_end(&mut buf)?;
            let trimmed = String::from_utf8_lossy(&buf).trim().to_string();
            if trimmed.is_empty() { "London".to_string() } else { trimmed }
        }
    };

    // In this format, the result only contains the weather and temperature,
    // without exposing the user location.
    //
    // For reference:
    //
    // curl 'wttr.in?format=1'
    // ☁️   +10°C
    //
    // curl 'wttr.in?format=2'
    // ☁️   🌡️+10°C 🌬️↘16km/h
    //
    // curl 'wttr.in?format=3'
    // city of london: ☁️   +10°C
    //
    // curl 'wttr.in?format=4'
    // city of london: ☁️   🌡️+10°C 🌬️↘16km
    let url = format!("https://wttr.in/{}?format=2", city);
    eprintln!("fetching weather from wttr.in");

    match cleanroom_sdk::http_get(&url, &[]) {
        Ok(response) => {
            let text = String::from_utf8_lossy(&response.body);
            print!("{text}");
        }
        Err(e) => {
            eprintln!("HTTP request failed: {e}");
            std::process::exit(1);
        }
    }

    Ok(())
}
