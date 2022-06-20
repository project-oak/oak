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

extern crate std;

use crate::message::{Message, RequestMessage};
use alloc::{collections::VecDeque, vec};

use super::*;

const BODY_LEN_MULTIPLICATOR: usize = 5;
const MOCK_LARGE_PAYLOAD_LEN: usize = frame::MAX_BODY_SIZE * BODY_LEN_MULTIPLICATOR;

fn mock_payload() -> Vec<u8> {
    let mut mock_payload: Vec<u8> = vec![0; MOCK_LARGE_PAYLOAD_LEN];

    // Fill the payload with increasing numbers, to ensure order is preserved.
    let mut x: u8 = 0;
    let filler = || {
        x = x.wrapping_add(1);
        x
    };
    mock_payload.fill_with(filler);
    mock_payload
}

#[test]
fn test_fragmenting_bytes_into_frames() {
    let payload = mock_payload();

    let mut frames = frame::bytes_into_frames(payload.clone());
    assert_eq!(frames.len(), BODY_LEN_MULTIPLICATOR);

    let mut reconstructed_payload: Vec<u8> = Vec::new();
    frames.iter_mut().for_each(|frame: &mut frame::Frame| {
        let _ = &mut reconstructed_payload.append(&mut frame.body);
    });
    assert_eq!(payload, reconstructed_payload);
}

#[test]
fn test_request_message_encoding() {
    let message = message::RequestMessage {
        method_id: 0,
        invocation_id: 0,
        body: mock_payload(),
    };
    let reconstructed_message = message::RequestMessage::decode(message.clone().encode());
    assert_eq!(message, reconstructed_message);
}

#[test]
fn test_response_message_encoding() {
    let message = message::ResponseMessage {
        status_code: 0,
        invocation_id: 0,
        body: mock_payload(),
    };
    let reconstructed_message = message::ResponseMessage::decode(message.clone().encode());
    assert_eq!(message, reconstructed_message);
}

#[derive(Default)]
struct MessageStore {
    inner: VecDeque<u8>,
}

impl ciborium_io::Read for MessageStore {
    type Error = anyhow::Error;

    fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
        buf.fill_with(|| self.inner.pop_front().unwrap());
        Ok(())
    }
}

impl ciborium_io::Write for MessageStore {
    type Error = anyhow::Error;
    fn write_all(&mut self, buf: &[u8]) -> Result<(), Self::Error> {
        self.inner.reserve(buf.len());
        self.inner.extend(buf);
        Ok(())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[test]
fn test_invocation_channel() {
    let mut invocation_channel = InvocationChannel::new(MessageStore::default());

    let message = message::RequestMessage {
        method_id: 0,
        invocation_id: 4,
        body: mock_payload(),
    };

    invocation_channel.write_message(message.clone()).unwrap();

    let reconstructed_message: RequestMessage = invocation_channel.read_message().unwrap();
    assert_eq!(message, reconstructed_message);
}

#[test]
fn test_invocation_channel_double_start_frame() {
    let mut invocation_channel = {
        let start_frame = {
            let mut frame = frame::Frame::default();
            frame.flags.set(frame::Flags::START, true);
            frame
        };
        let mut frame_store = frame::Framed::new(MessageStore::default());
        frame_store.write_frame(start_frame.clone()).unwrap();
        frame_store.write_frame(start_frame).unwrap();
        InvocationChannel { inner: frame_store }
    };

    invocation_channel
        .read_message::<message::RequestMessage>()
        .unwrap_err();
}

#[test]
fn test_invocation_channel_expected_start_frame() {
    let mut invocation_channel = {
        let end_frame = {
            let mut frame = frame::Frame::default();
            frame.flags.set(frame::Flags::END, true);
            frame
        };
        let mut frame_store = frame::Framed::new(MessageStore::default());
        frame_store.write_frame(end_frame).unwrap();
        InvocationChannel { inner: frame_store }
    };

    invocation_channel
        .read_message::<message::RequestMessage>()
        .unwrap_err();
}
