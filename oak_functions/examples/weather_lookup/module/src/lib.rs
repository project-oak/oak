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
// Required for enabling benchmark tests.
#![feature(test)]

use location_utils::{
    cell_id_to_bytes, find_cell, location_from_bytes, location_from_degrees, location_to_bytes,
    Angle, LatLng, DEFAULT_CUTOFF_RADIUS_RADIANS,
};
use oak_functions::log;
use serde::Deserialize;

#[cfg(test)]
mod tests;

#[derive(Deserialize, Debug)]
struct Request {
    #[serde(rename = "lat")]
    latitude_degrees: f64,
    #[serde(rename = "lng")]
    longitude_degrees: f64,
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
        log!("parsed request: {:?}\n", request);

        // Find the S2 cell (using the default level) that contains the current location.
        let level = location_utils::S2_DEFAULT_LEVEL;
        let location = location_from_degrees(request.latitude_degrees, request.longitude_degrees);
        let cell =
            find_cell(&location, level).map_err(|err| format!("could not find cell: {:?}", err))?;
        log!("current location cell token: {}\n", cell.to_token());

        // Look up the index values for the list of weather data points in the vicinity of the cell.
        let index = oak_functions::storage_get_item(&cell_id_to_bytes(&cell))
            .map_err(|err| format!("could not get index item: {:?}", err))?
            .ok_or("could not find index item for cell")?;

        // Find the closest key by linearly scanning the nearby weather data points to find the
        // closest one.
        let mut best_distance = Angle::from(DEFAULT_CUTOFF_RADIUS_RADIANS);
        let mut best_location: Option<LatLng> = None;

        for chunk in index.chunks(8) {
            let test = location_from_bytes(chunk)
                .map_err(|err| format!("could not convert chunk to location: {:?}", err))?;
            let distance = location.distance(&test);
            if distance < best_distance {
                best_distance = distance;
                best_location = Some(test);
            }
        }

        let result = match best_location {
            Some(key_location) => {
                log!("nearest data point: {:?}\n", key_location);
                let best_value = oak_functions::storage_get_item(&location_to_bytes(&key_location))
                    .map_err(|err| format!("could not get item: {:?}", err))?
                    .ok_or("could not find item with key")?;
                log!("nearest location value: {:?}\n", best_value);

                best_value
            }
            None => b"could not find location within cutoff".to_vec(),
        };

        result
    };

    let response = result.unwrap_or_else(|err| err.as_bytes().to_vec());

    // Write the response.
    oak_functions::write_response(&response).expect("Couldn't write the response body.");
}
