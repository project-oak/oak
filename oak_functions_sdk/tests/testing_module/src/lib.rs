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

#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn main() {
    // Read the message to echo from the request.
    let request = oak_functions_sdk::read_request().expect("couldn't read request body");
    let request = String::from_utf8(request).expect("couldn't parse request");

    match request.as_str() {
        "ECHO" => {
            // We invoke the Testing extension with an EchoRequest.
            // Note that the message to echo is the request itself.
            let echo_response = oak_functions_sdk::testing(request.as_bytes(), true)
                .expect("couldn't invoke testing");
            oak_functions_sdk::write_response(&echo_response)
                .expect("couldn't write response body");
        }
        "BLACKHOLE" => {
            // Keep in sync with test_blackhole in
            // `workspace/oak_functions/sdk/oak_functions/tests/integration_test.rs`.
            let blackhole_response = oak_functions_sdk::testing(request.as_bytes(), false)
                .expect("couldn't invoke testing");
            // We expect an empty response, because blackhole does not give back a result.
            assert!(blackhole_response.is_empty());

            // If we reached here, the assert did not fail and we send a response back. This
            // helps us to distinguish from a failure in the Wasm module, where
            // also an empty response would be sent.
            oak_functions_sdk::write_response("Blackholed".as_bytes())
                .expect("couldn't write response body");
        }
        "HUGE_RESPONSE" => {
            // Ignore request just send a huge response.
            let bytes: Vec<u8> = (0..i32::pow(2, 20)).map(|_| 42u8).collect();
            oak_functions_sdk::write_response(&bytes).expect("couldn't write response body");
        }
        _ => panic!("request not recognized"),
    }
}
