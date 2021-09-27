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

//! Oak Functions Hello World example.

const CLIENT_HELLO_WORLD: &str = "Client Hello World";
const SERVER_HELLO_WORLD: &str = "Server Hello World";

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Read the request.
    let request_body = oak_functions::read_request().expect("Couldn't read request body");
    let parsed_request = std::str::from_utf8(&request_body).expect("Couldn't parse request body");
    assert_eq!(parsed_request, CLIENT_HELLO_WORLD);

    // Write the response.
    let response = SERVER_HELLO_WORLD.as_bytes().to_vec();
    oak_functions::write_response(&response).expect("Couldn't write the response body");
}
