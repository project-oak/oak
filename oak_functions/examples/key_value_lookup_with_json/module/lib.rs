//
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
//

//! Oak Functions key / value lookup example with JSON request and response.
//!
//! Request format:  `{"key": <integer>}`
//! Response format: `{"value": <integer>}`

extern crate alloc;

use serde::{Deserialize, Serialize};

/// JSON schema for the lookup request.
#[derive(Debug, Deserialize)]
struct LookupRequest {
    key: String,
}

/// JSON schema for the lookup response.
#[derive(Debug, Serialize)]
struct LookupResponse {
    value: String,
}

#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn main() {
    let request = oak_functions_sdk::read_request().expect("couldn't read request body");

    // Deserialize the JSON request.
    let lookup_request: LookupRequest =
        serde_json::from_slice(&request).expect("couldn't parse JSON request");

    let value_bytes = oak_functions_sdk::storage_get_item(lookup_request.key.as_bytes())
        .expect("couldn't look up entry")
        .unwrap_or_default();

    // Serialize the JSON response.
    let lookup_response = LookupResponse { value: String::from_utf8(value_bytes).unwrap() };

    let response = serde_json::to_vec(&lookup_response).expect("couldn't serialize JSON response");

    oak_functions_sdk::write_response(&response).expect("couldn't write response body");
}
