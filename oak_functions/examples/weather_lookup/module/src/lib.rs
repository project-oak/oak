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

use location_utils::{find_cell, IndexValue};
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
        log!("parsed request: {:?}\n", request);

        let cell = find_cell(request.latitude_degrees, request.longitude_degrees)?;
        log!("current location cell: {:?}\n", cell);
        let position = cell.relative_position(request.latitude_degrees, request.longitude_degrees);
        log!("position relative to cell midpoint: {:?}\n", position);

        // Look up the index values for the list of weather stations in the vicinity of the cell.
        let index = oak_functions::storage_get_item(&cell.index.to_bytes())
            .map_err(|err| format!("could not get index item: {:?}", err))?
            .ok_or("could not find index item for cell")?;

        // Find the closest key by linearly scanning the nearby weather stations to find the closest
        // one.
        let best_key = index
            .chunks(16)
            .min_by_key(|key| {
                let station = IndexValue::from_bytes(key);
                station.position.squared_distance(&position)
            })
            .ok_or("could not find nearest location")?;
        log!("nearest station key: {:?}\n", best_key);
        let best_station = IndexValue::from_bytes(&best_key);
        log!("nearest station: {:?}\n", best_station);
        // Make sure it is no further than 40km.
        position.validate_close_enough(&best_station.position, 40_000)?;

        let best_value = oak_functions::storage_get_item(&best_station.value_key)
            .map_err(|err| format!("could not get item: {:?}", err))?
            .ok_or("could not find item with key")?;
        log!("nearest location value: {:?}\n", best_value);

        best_value
    };

    let response = result.unwrap_or_else(|err| err.as_bytes().to_vec());

    // Write the response.
    oak_functions::write_response(&response).expect("Couldn't write the response body.");
}
