//
// Copyright 2018 The Project Oak Authors
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

extern crate oak_tests;

use crate::*;

#[test]
fn test_status_from_i32() {
    assert_eq!(Status::InvalidArgs, status_from_i32(2));
    assert_eq!(Status::Unknown(42), status_from_i32(42));
}

#[test]
fn test_result_from_status() {
    assert_matches!(result_from_status(Status::Ok, 12), Ok(12));
    assert_matches!(result_from_status(Status::Unknown(42), 12), Err(_));
}

#[test]
fn test_write_message() {
    let mut send_channel = SendChannelHalf::new(123);
    let data = [0x44, 0x4d, 0x44];
    assert_matches!(send_channel.write_message(&data), Ok(()));
    assert_eq!("DMD", oak_tests::last_message());
}

#[test]
fn test_write() {
    writeln!(logging_channel(), "ABC").unwrap();
    assert_eq!("ABC\n", oak_tests::last_message());
    assert_matches!(logging_channel().flush(), Ok(()));
}

// TODO: test_read_message

#[test]
fn test_channel_pair() {
    let mut pair = ChannelPair::new(1, 2);
    let data = [0x44, 0x44];
    assert_matches!(pair.send.write_message(&data), Ok(()));
    assert_eq!("DD", oak_tests::last_message());
}

struct TestNode;
impl Node for TestNode {
    fn new() -> Self {
        TestNode
    }
    fn invoke(&mut self, _grpc_method_name: &str, _grpc_pair: &mut ChannelPair) {}
}

#[test]
fn test_set_node() {
    assert_eq!(false, have_node());
    set_node::<TestNode>();
    assert_eq!(true, have_node());
}

#[test]
#[should_panic]
fn test_set_node_twice() {
    set_node::<TestNode>();
    set_node::<TestNode>(); // panic!
}

#[test]
fn test_handle_grpc_call() {
    set_node::<TestNode>();
    assert_eq!(true, have_node());
    oak_handle_grpc_call();
}

#[test]
#[should_panic]
fn test_handle_grpc_call_no_node() {
    oak_handle_grpc_call(); // no node: panic!
}
