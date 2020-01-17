//
// Copyright 2019 The Project Oak Authors
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

use crate::proto::hello_world::{HelloRequest, HelloResponse};
use crate::proto::hello_world_grpc::HelloWorldNode;
use assert_matches::assert_matches;
use oak::grpc;
use oak::grpc::OakNode;
use oak::OakStatus;
use serial_test_derive::serial;

// Test invoking a Node service method directly.
#[test]
fn test_direct_hello_request() {
    let mut node = crate::Node::new();
    let mut req = HelloRequest::new();
    req.set_greeting("world".to_string());
    let result = node.say_hello(req);
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().reply);
}

#[test]
#[serial(node_test)]
fn test_no_handle() {
    oak_tests::start_node(oak_abi::INVALID_HANDLE, crate::inner_main);
    assert_eq!(Err(OakStatus::ERR_CHANNEL_CLOSED), oak_tests::stop());
}

// Test invoking a Node service method via the Oak entrypoints.
#[test]
#[serial(node_test)]
fn test_hello_request() {
    let handle = oak_tests::grpc_channel_setup_default();
    oak_tests::start_node(handle, crate::inner_main);

    let mut req = HelloRequest::new();
    req.set_greeting("world".to_string());
    let result: grpc::Result<HelloResponse> =
        oak_tests::inject_grpc_request("/oak.examples.hello_world.HelloWorld/SayHello", req);
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().reply);

    assert_eq!(Err(OakStatus::ERR_TERMINATED), oak_tests::stop());
}
