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

use oak_functions::log;
use serde::Deserialize;

#[cfg(test)]
mod tests;

#[derive(Deserialize, Debug)]
struct Request {
    #[serde(rename = "lat")]
    latitude_degrees: f32,
    #[serde(rename = "lon")]
    longitude_degrees: f32,
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Produce a result which is either a successful response (as raw bytes), or an error message to
    // return to the client (as a human-readable string).
    let result: Result<Vec<u8>, String> = try {
        // Read the request.
        let request_body = oak_functions::read_request()
            .map_err(|err| format!("could not read request body: {:?}", err))?;

        // Parse the request as JSON.
        let request: Request = serde_json::from_slice(&request_body)
            .map_err(|err| format!("could not deserialize request as JSON: {:?}", err))?;
        log!("parsed request: {:?}\n", request).unwrap();

        // Fetch the index entry, containing all the concatenated keys.
        let index = oak_functions::storage_get_item("index".as_bytes())
            .map_err(|err| format!("could not get item: {:?}", err))?
            .ok_or("could not find index item")?;

        // Build a `Location` object from the client request.
        let request_location = Location {
            latitude_millidegrees: (request.latitude_degrees * 1000.0) as i32,
            longitude_millidegrees: (request.longitude_degrees * 1000.0) as i32,
        };
        log!("request location: {:?}\n", request_location).unwrap();

        // Find the closest key by linearly scanning the keys from the index and computing their
        // distance to the client request location.
        let best_key = index
            .chunks(8)
            .min_by_key(|key| {
                let location = Location::from_bytes(key);
                location.distance(&request_location)
            })
            .ok_or("could not find nearest location")?;
        log!("nearest location key: {:?}\n", best_key).unwrap();
        log!("nearest location: {:?}\n", Location::from_bytes(&best_key)).unwrap();

        let best_value = oak_functions::storage_get_item(best_key)
            .map_err(|err| format!("could not get item: {:?}", err))?
            .ok_or("could not find item with key")?;
        log!("nearest location value: {:?}\n", best_value).unwrap();

        best_value
    };

    let response = result.unwrap_or_else(|err| err.as_bytes().to_vec());

    // Write the response.
    oak_functions::write_response(&response).expect("Couldn't write the response body.");
}

/// We use a fixed point representation (`i32`, instead of `f32`) for the location coordinates in
/// order to be more efficient at parsing it from bytes, and also to compute distance via arithmetic
/// operations.
#[derive(Debug, Eq, PartialEq)]
struct Location {
    latitude_millidegrees: i32,
    longitude_millidegrees: i32,
}

impl Location {
    fn from_bytes(c: &[u8]) -> Location {
        let mut latitude_millidegrees_bytes = [0; 4];
        latitude_millidegrees_bytes.copy_from_slice(&c[0..4]);
        let mut longitude_millidegrees_bytes = [0; 4];
        longitude_millidegrees_bytes.copy_from_slice(&c[4..8]);

        Location {
            latitude_millidegrees: i32::from_be_bytes(latitude_millidegrees_bytes),
            longitude_millidegrees: i32::from_be_bytes(longitude_millidegrees_bytes),
        }
    }

    #[cfg(test)]
    fn to_bytes(&self) -> Vec<u8> {
        [
            self.latitude_millidegrees.to_be_bytes(),
            self.longitude_millidegrees.to_be_bytes(),
        ]
        .concat()
    }

    fn distance(&self, other: &Location) -> i32 {
        // TODO(#2201): Improve distance calculation logic.

        // Convert to `i64` in order to avoid overflow when squaring.
        (((self.latitude_millidegrees as i64 - other.latitude_millidegrees as i64).pow(2)
            + (self.longitude_millidegrees as i64 - other.longitude_millidegrees as i64).pow(2))
            as f32)
            .sqrt() as i32
    }
}
