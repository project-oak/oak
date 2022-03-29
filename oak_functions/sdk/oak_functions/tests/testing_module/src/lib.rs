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
use serde_derive::{Deserialize, Serialize};

// TestingMessage needs to be kept in sync with TestingMessage in testing extension.
#[derive(Serialize, Deserialize)]
pub enum TestingMessage {
    EchoRequest(String),
    EchoResponse(String),
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    // Read the message to echo from the request.
    let request = oak_functions::read_request().expect("Fail to read request body.");
    let message_to_echo = String::from_utf8(request).expect("Fail to parse request");

    // Serialze a EchoRequest with the message_to_echo.
    let echo_request = bincode::serialize(&TestingMessage::EchoRequest(message_to_echo))
        .expect("Fail to serialize testing message.");
    // We invoke the Testing extension with an EchoRequest.
    let serialized_echo_response = oak_functions::invoke(echo_request)
        .expect("Fail to invoke_testing")
        .expect("No result returned.");

    let echo_response = bincode::deserialize(&serialized_echo_response)
        .expect("Fail to deserialize testing message.");

    let response_body = match echo_response {
        // Make sure we received a EchoResponse.
        TestingMessage::EchoResponse(echoed_message) => echoed_message,
        _ => String::from("Fail to receive an echo response"),
    };

    oak_functions::write_response(response_body.as_bytes()).expect("Couldn't write response body.");
}
