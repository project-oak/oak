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

//! Oak functions hello world example. Responds with `Hello $request_body!` to every request.

#[cfg(test)]
mod tests;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Read the request
    let request_body = oak_functions::read_request().expect("Couldn't read request body.");

    // Create response body
    let response_body = format!(
        "Hello {}!\n",
        std::str::from_utf8(&request_body).expect("Couldn't convert bytes to string")
    );

    // Write the response body
    oak_functions::write_response_body(&response_body.as_bytes())
        .expect("Couldn't write the response body.");
}
