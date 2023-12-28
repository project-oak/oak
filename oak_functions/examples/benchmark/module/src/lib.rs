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

use oak_functions_proto::oak::oak_functions::benchmark::{
    benchmark_request::Action, BenchmarkRequest, EchoAndPanicTest, LookupTest,
};
use prost::Message;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let request = oak_functions_sdk::read_request().expect("couldn't read request body");
    let request = BenchmarkRequest::decode(&*request).expect("couldn't decode request");

    match request.action.unwrap() {
        Action::Lookup(LookupTest { key }) => {
            let mut response = Vec::new();
            for _ in 0..request.iterations {
                response = oak_functions_sdk::storage_get_item(&key)
                    .expect("couldn't look up entry")
                    .unwrap_or_default();
            }
            oak_functions_sdk::write_response(&response).expect("couldn't write response body");
        }
        Action::EchoAndPanic(EchoAndPanicTest { data }) => {
            oak_functions_sdk::write_response(&data).expect("couldn't write response body");
            panic!("panic requested");
        }
    };
}
