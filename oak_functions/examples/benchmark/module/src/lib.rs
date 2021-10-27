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

//! Oak Functions benchmark example.
pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.functions.benchmark.rs"));
}

use prost::Message;
use proto::{benchmark_request::Action, BenchmarkRequest, LookupTest};

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let request = oak_functions::read_request().expect("Couldn't read request body.");
    let request = BenchmarkRequest::decode(&*request).expect("Couldn't decode request.");

    match request.action.unwrap() {
        Action::Lookup(LookupTest { key }) => {
            let mut response = Vec::new();
            for _ in 0..request.iterations {
                response = oak_functions::storage_get_item(&key)
                    .expect("Couldn't look up entry")
                    .unwrap_or_default();
            }
            oak_functions::write_response(&response).expect("Couldn't write response body.");
        }
    };
}
