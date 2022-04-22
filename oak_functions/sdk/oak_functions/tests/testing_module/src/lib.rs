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

//! Oak Functions ABI test for Testing Extension.

use oak_functions_abi::{TestingRequest, TestingResponse};

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Read the message to echo from the request.
    let request = oak_functions::read_request().expect("Fail to read request body.");
    let request = String::from_utf8(request).expect("Fail to parse request");

    match request.as_str() {
        "ECHO" => {
            // Serialize a EchoRequest. Note that the message to echo is the request itself.
            let echo_request = bincode::serialize(&TestingRequest::Echo(request))
                .expect("Fail to serialize testing message.");
            // We invoke the Testing extension with an EchoRequest.
            let serialized_echo_response =
                oak_functions::testing(&echo_request).expect("Fail to invoke testing.");

            let echo_response = bincode::deserialize(&serialized_echo_response)
                .expect("Fail to deserialize testing message.");

            let TestingResponse::Echo(response_body) = echo_response;

            oak_functions::write_response(response_body.as_bytes())
                .expect("Fail to write response body.");
        }
        "BLACKHOLE" => {
            // Keep in sync with test_blackhole in
            // `workspace/oak_functions/sdk/oak_functions/tests/integration_test.rs`.
            let blackhole_request = bincode::serialize(&TestingRequest::Blackhole(request))
                .expect("Fail to serialize testing message.");

            let blackhole_response =
                oak_functions::testing(&blackhole_request).expect("Fail to invoke testing.");
            // We expect an empty response, because blackhole does not give back a result.
            assert!(blackhole_response.is_empty());

            // If we reached here, the assert did not fail and we send a response back. This helps
            // us to distinguish from a failure in the Wasm module, where also an
            // empty response would be sent.
            oak_functions::write_response("Blackholed".as_bytes())
                .expect("Fail to write response body.");
        }
        _ => panic!("Request not recognized"),
    }
}
