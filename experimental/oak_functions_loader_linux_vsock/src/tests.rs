//
// Copyright 2022 The Project Oak Authors
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

use crate::channel::Channel;
use assert_matches::assert_matches;
use oak_baremetal_communication_channel::{Read, Write};
use std::io::Cursor;

const TEST_MESSAGE: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

#[test]
fn test_channel() {
    let mut write_buffer = vec![];

    let write_stream = Cursor::new(&mut write_buffer);
    let mut write_channel = Channel::new(write_stream);

    let write_result = write_channel.write(&TEST_MESSAGE);
    assert_matches!(write_result, Ok(_));

    let mut read_buffer: Vec<u8> = write_buffer.to_vec();
    let read_stream = Cursor::new(&mut read_buffer);
    let mut read_channel = Channel::new(read_stream);

    let mut message_buffer = vec![0; TEST_MESSAGE.len()];
    let read_result = read_channel.read(&mut message_buffer);
    assert_matches!(read_result, Ok(_));
    assert_eq!(&TEST_MESSAGE[..], message_buffer);
}
