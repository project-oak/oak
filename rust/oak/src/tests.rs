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
    oak_tests::reset_channels();
    let mut send_channel = SendChannelHalf::new(123);
    let data = [0x44, 0x4d, 0x44];
    assert_matches!(send_channel.write_message(&data), Ok(()));
    assert_eq!("DMD", oak_tests::last_message_as_string());
}

#[test]
fn test_write_message_failure() {
    oak_tests::reset_channels();
    let mut send_channel = SendChannelHalf::new(123);
    let data = [0x44, 0x4d, 0x44];
    oak_tests::set_write_status(Some(99));
    assert_matches!(send_channel.write_message(&data), Err(_));
}

#[test]
fn test_write() {
    oak_tests::reset_channels();
    writeln!(logging_channel(), "ABC").unwrap();
    assert_eq!("ABC\n", oak_tests::last_message_as_string());
    assert_matches!(logging_channel().flush(), Ok(()));
}

#[test]
fn test_read_message() {
    oak_tests::reset_channels();
    let mut send = SendChannelHalf::new(123);
    let data = [0x44, 0x4d, 0x44];
    assert_matches!(send.write_message(&data), Ok(()));
    assert_matches!(send.write_message(&data), Ok(()));

    let mut rcv = ReceiveChannelHalf::new(123);
    let mut buf = Vec::with_capacity(1);
    assert_matches!(rcv.read_message(&mut buf), Ok(3));
    assert_eq!(data.to_vec(), buf);

    let mut big_buf = Vec::with_capacity(100);
    assert_matches!(rcv.read_message(&mut big_buf), Ok(3));
    assert_eq!(data.to_vec(), big_buf);
}

#[test]
fn test_read_message_failure() {
    oak_tests::reset_channels();
    let mut rcv = ReceiveChannelHalf::new(123);
    let mut buf = Vec::with_capacity(100);
    oak_tests::set_read_status(Some(99));
    assert_matches!(rcv.read_message(&mut buf), Err(_));
}

#[test]
fn test_read_message_internal_failure() {
    oak_tests::reset_channels();
    let mut rcv = ReceiveChannelHalf::new(123);
    let mut buf = Vec::with_capacity(100);

    // Set buffer too small but don't set actual size, so the retry gets confused.
    oak_tests::set_read_status(Some(oak_tests::STATUS_ERR_BUFFER_TOO_SMALL));
    assert_matches!(rcv.read_message(&mut buf), Err(_));
}

#[test]
fn test_channel_pair() {
    oak_tests::reset_channels();
    let mut pair = ChannelPair::new(1, 2);
    let data = [0x44, 0x44];
    assert_matches!(pair.send.write_message(&data), Ok(()));
    assert_eq!("DD", oak_tests::last_message_as_string());
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
    reset_node();
    assert_eq!(false, have_node());
    set_node::<TestNode>();
    assert_eq!(true, have_node());
}

#[test]
#[should_panic]
fn test_set_node_twice() {
    reset_node();
    set_node::<TestNode>();
    set_node::<TestNode>(); // panic!
}

#[test]
fn test_handle_grpc_call() {
    reset_node();
    set_node::<TestNode>();
    assert_eq!(true, have_node());
    oak_handle_grpc_call();
}

#[test]
#[should_panic]
// TODO: Re-enable when https://github.com/project-oak/oak/issues/161 is fixed.
#[ignore]
fn test_handle_grpc_call_no_node() {
    reset_node();
    oak_handle_grpc_call(); // no node: panic!
}
