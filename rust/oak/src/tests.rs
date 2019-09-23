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
use std::io::Write;

#[test]
fn test_write_message() {
    oak_tests::reset_channels();
    let send_channel = WriteHandle { handle: 123 };
    let data = [0x44, 0x4d, 0x44];
    assert_eq!(OakStatus::OK, channel_write(send_channel, &data, &[]));
    assert_eq!("DMD", oak_tests::last_message_as_string());
}

#[test]
fn test_write_message_failure() {
    oak_tests::reset_channels();
    let send_channel = WriteHandle { handle: 123 };
    let data = [0x44, 0x4d, 0x44];
    oak_tests::set_write_status(Some(OakStatus::ERR_INVALID_ARGS.value()));
    assert_eq!(
        OakStatus::ERR_INVALID_ARGS,
        channel_write(send_channel, &data, &[])
    );
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
    let send = WriteHandle { handle: 123 };
    let data = [0x44, 0x4d, 0x44];
    assert_eq!(OakStatus::OK, channel_write(send, &data, &[]));
    assert_eq!(OakStatus::OK, channel_write(send, &data, &[]));

    let rcv = ReadHandle { handle: 123 };
    let mut buf = Vec::with_capacity(1);
    let mut handles = Vec::with_capacity(1);
    assert_matches!(channel_read(rcv, &mut buf, &mut handles), OakStatus::OK);
    assert_eq!(data.to_vec(), buf);

    let mut big_buf = Vec::with_capacity(100);
    assert_matches!(channel_read(rcv, &mut big_buf, &mut handles), OakStatus::OK);
    assert_eq!(data.to_vec(), big_buf);
}

#[test]
fn test_read_message_failure() {
    oak_tests::reset_channels();
    let rcv = ReadHandle { handle: 123 };
    let mut buf = Vec::with_capacity(100);
    let mut handles = Vec::with_capacity(1);
    oak_tests::set_read_status(Some(OakStatus::ERR_INVALID_ARGS.value()));
    assert_eq!(
        channel_read(rcv, &mut buf, &mut handles),
        OakStatus::ERR_INVALID_ARGS
    );
}

#[test]
fn test_read_message_internal_failure() {
    oak_tests::reset_channels();
    let rcv = ReadHandle { handle: 123 };
    let mut buf = Vec::with_capacity(100);
    let mut handles = Vec::with_capacity(1);

    // Set buffer too small but don't set actual size, so the retry gets confused.
    oak_tests::set_read_status(Some(OakStatus::ERR_BUFFER_TOO_SMALL.value()));
    assert_matches!(
        channel_read(rcv, &mut buf, &mut handles),
        OakStatus::ERR_BUFFER_TOO_SMALL
    );
}

#[test]
fn test_handle_space() {
    let h = vec![ReadHandle { handle: 1 }, ReadHandle { handle: 2 }];
    let data = [
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00,
    ];
    let mut space = new_handle_space(&h);
    assert_eq!(data.to_vec(), space);
    space[8] = 1;
    prep_handle_space(&mut space);
    assert_eq!(data.to_vec(), space);
}
