//
// Copyright 2021 The Project Oak Authors
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
//

//! Oak Functions weather lookup example.

#![feature(try_blocks)]

use serde::Deserialize;

#[cfg(test)]
mod tests;

#[derive(Deserialize)]
struct Location {
    #[serde(rename = "lat")]
    latitude_degrees: i32,
    #[serde(rename = "lon")]
    longitude_degrees: i32,
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Produce a result which is either a successful response (as raw bytes), or an error message to
    // return to the client (as a human-readable string).
    let result: Result<Vec<u8>, &str> = try {
        // Read the request.
        let request_body =
            oak_functions::read_request().map_err(|_err| "Couldn't read request body.")?;
        // Parse the request as a `Location` JSON object.
        let location: Location = serde_json::from_slice(&request_body)
            .map_err(|_err| "could not deserialize request as JSON")?;
        // Format the location as `lat,lon` in order to perform a lookup.
        let key = format!(
            "{},{}",
            location.latitude_degrees, location.longitude_degrees
        );
        // Try to look up the location in the storage data, and if found use the result as the
        // response message.
        let response = oak_functions::storage_get_item(key.as_bytes())
            .map_err(|_err| "Couldn't look up weather")?
            .ok_or("weather not found for location")?;
        response
    };

    let response = result.unwrap_or_else(|err| err.as_bytes().to_vec());

    // Write the response.
    oak_functions::write_response(&response).expect("Couldn't write the response body.");
}
