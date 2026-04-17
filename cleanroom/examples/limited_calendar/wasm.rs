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

use std::{
    io::{self, Read},
    time::{SystemTime, UNIX_EPOCH},
};

fn main() -> io::Result<()> {
    // 1. Get current time (just to show we can, and for logging)
    let now = SystemTime::now();
    let now_secs = now
        .duration_since(UNIX_EPOCH)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?
        .as_secs();
    eprintln!("Current time: {} seconds since epoch", now_secs);

    // 2. Read API key (requires {calendar_token} in computation secrecy)
    let token = cleanroom_sdk::read_cell("google_oauth_token").ok_or_else(|| {
        io::Error::new(io::ErrorKind::Other, "Could not read google_oauth_token from cell")
    })?;

    // Read calendar ID from stdin.
    let mut stdin_bytes = Vec::new();
    io::stdin().read_to_end(&mut stdin_bytes)?;
    let calendar_id = String::from_utf8_lossy(&stdin_bytes);
    let calendar_id = calendar_id.trim();
    if calendar_id.is_empty() {
        return Err(io::Error::new(io::ErrorKind::Other, "calendar ID cannot be empty"));
    }

    // 3. Make HTTP request to Google Calendar API.
    let url = format!(
        "https://www.googleapis.com/calendar/v3/calendars/{}/events?timeMin=2014-03-30T00:00:00Z&timeMax=2014-04-19T23:59:59Z",
        calendar_id
    );
    eprintln!("Fetching calendar events from Google for {}...", calendar_id);
    let bearer = format!("Bearer {}", token);
    let response = cleanroom_sdk::http_get(&url, &[("Authorization", &bearer)])
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;

    if response.status != 200 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("HTTP error: {}", response.status),
        ));
    }

    let body = &response.body;

    // 4. Parse JSON and filter events
    let v: serde_json::Value = serde_json::from_slice(body)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?;

    let items = v["items"].as_array().ok_or_else(|| {
        io::Error::new(io::ErrorKind::Other, "Expected 'items' array in response")
    })?;

    let date_lower_limit = "2014-03-30T00:00:00Z";
    let date_upper_limit = "2014-04-19T23:59:59Z";

    let mut output = String::from(
        "Calendar events between 2014-03-30 and 2014-04-19 (simulated current date: 2014-04-09):\n",
    );
    for item in items {
        let summary = item["summary"].as_str().unwrap_or("No Summary");
        let start = &item["start"];
        let date_time_str = start["dateTime"].as_str().or_else(|| start["date"].as_str());

        if let Some(dt_str) = date_time_str {
            if dt_str >= date_lower_limit && dt_str <= date_upper_limit {
                output.push_str(&format!("- {} (at {})\n", summary, dt_str));
            }
        }
    }

    // 5. Write filtered output.
    print!("{output}");

    Ok(())
}
