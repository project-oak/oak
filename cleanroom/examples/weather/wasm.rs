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

/// Fetches weather from wttr.in via WASI HTTP.
///
/// Reads a city name from the `user_location` cell (in the
/// `user_location` IFC category), fetches weather data for that
/// city, and explicitly declassifies the output before returning it.
fn main() -> io::Result<()> {
    // Because this module reads from the "user_location" cell, its computation
    // label automatically becomes tainted with that label. It will look at the
    // policy deciding whether to allow output.

    // 1. Read the labeled data from the cell store.
    let city = match cleanroom_sdk::get_cell("user_location") {
        Some(val) => val,
        None => {
            // Fall back to reading from stdin.
            let mut buf = String::new();
            io::stdin().read_to_string(&mut buf)?;
            let trimmed = buf.trim().to_string();
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
    // city of london: ☁️   🌡️+10°C 🌬️↘16km/h
    let url = format!("https://wttr.in/{}?format=2", city);
    eprintln!("Fetching weather from wttr.in");

    // Declassify user_location before making the network request.
    // The URL format (format=2) does not include the city name in
    // the response, so the output does not leak the user's location.
    cleanroom_sdk::declassify(&["user_location"]);

    match waki::Client::new().get(&url).send() {
        Ok(response) => {
            let body = response.body().unwrap_or_default();
            let text = String::from_utf8_lossy(&body);
            print!("{}", text);
        }
        Err(e) => {
            eprintln!("HTTP request failed: {}", e);
            std::process::exit(1);
        }
    }

    Ok(())
}
