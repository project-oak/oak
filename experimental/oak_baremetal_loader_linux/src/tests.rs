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
use oak_baremetal_communication_channel::{Read, Write};
use std::{
    io::{BufReader, BufWriter, Cursor},
};

const TEST_BUFFER_SIZE: usize = 1024;
const TEST_MESSAGE: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

#[test]
fn test_channel() {
    let buffer = vec![0; TEST_BUFFER_SIZE];
    let mut stream = Cursor::new(buffer);
    let mut channel = Channel::new(stream);

    let write_result = channel.write(&TEST_MESSAGE);
    assert!(write_result.is_ok());

    // // Start reading from the same stream.
    // stream.set_position(0);

    // Write the message back to the stream.

    let mut message_buffer = vec![0; TEST_MESSAGE.len()];
    let read_result = channel.read(&mut message_buffer);
    assert!(read_result.is_ok());
    assert_eq!(&TEST_MESSAGE[..], message_buffer);
}
