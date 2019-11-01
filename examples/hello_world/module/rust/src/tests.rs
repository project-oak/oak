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

use oak::grpc;
use oak::grpc::OakNode;
use oak::OakStatus;
use proto::hello_world::{HelloRequest, HelloResponse};
use proto::hello_world_grpc::HelloWorldNode;

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
fn test_no_handle_mapping() {
    // Run the Node without preparing a handle for the "grpc_in" port name.
    oak_tests::start_node(oak_tests::DEFAULT_NODE_NAME);
    assert_eq!(OakStatus::ERR_CHANNEL_CLOSED, oak_tests::stop());
}

// Test invoking a Node service method via the Oak entrypoints.
#[test]
#[serial(node_test)]
fn test_hello_request() {
    oak_tests::grpc_channel_setup_default();
    oak_tests::start_node(oak_tests::DEFAULT_NODE_NAME);

    let mut req = HelloRequest::new();
    req.set_greeting("world".to_string());
    let result: grpc::Result<HelloResponse> =
        oak_tests::inject_grpc_request("/oak.examples.hello_world.HelloWorld/SayHello", req);
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().reply);

    assert_eq!(OakStatus::ERR_TERMINATED, oak_tests::stop());
}
