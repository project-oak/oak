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

//! Oak Functions key / value lookup example.

use oak_proto_rust::oak::oak_functions::benchmark::{
    lookup_request::Mode, LookupRequest, LookupResponse,
};
use prost::Message;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let request_bytes = oak_functions_sdk::read_request().expect("couldn't read request body");
    let request = LookupRequest::decode(request_bytes.as_ref()).expect("couldn't decode request");

    // Implicitly convert not found entries to empty values.
    let values: Vec<Vec<u8>> = match request.mode() {
        // Look up individual keys one by one and collect the results.
        Mode::Individual => request
            .keys
            .into_iter()
            .map(|key| {
                oak_functions_sdk::storage_get_item(&key)
                    .expect("couldn't look up entry")
                    .unwrap_or_default()
            })
            .collect(),
        // Look up all keys in a batch.
        Mode::Batch => oak_functions_sdk::storage_get_items(request.keys)
            .expect("couldn't look up entries")
            .into_iter()
            .map(|v| v.unwrap_or_default())
            .collect(),
    };

    let response = LookupResponse { values };
    let response_bytes = response.encode_to_vec();
    oak_functions_sdk::write_response(&response_bytes).expect("couldn't write response body");
}
