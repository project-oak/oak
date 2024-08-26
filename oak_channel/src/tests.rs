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

#![allow(clippy::box_default)]

extern crate std;

use alloc::{collections::VecDeque, vec};

use super::*;
use crate::message::{Message, RequestMessage};

const BODY_LEN_MULTIPLIER: usize = 5;
const MOCK_LARGE_PAYLOAD_LEN: usize = frame::MAX_BODY_SIZE * BODY_LEN_MULTIPLIER;

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

    let mut frames = frame::bytes_into_frames(&payload).unwrap();
    assert_eq!(frames.len(), BODY_LEN_MULTIPLIER);

    let mut reconstructed_payload: Vec<u8> = Vec::new();
    frames.iter_mut().for_each(|frame: &mut frame::Frame| {
        assert!(frame.body.len() <= frame::MAX_BODY_SIZE);
        let _ = &mut reconstructed_payload.extend_from_slice(frame.body);
    });
    assert_eq!(payload, reconstructed_payload);
}

#[test]
fn test_request_message_encoding() {
    let message = message::RequestMessage { invocation_id: 0, body: mock_payload() };
    let reconstructed_message = message::RequestMessage::decode(&message.clone().encode());
    assert_eq!(message, reconstructed_message);
}

#[test]
fn test_response_message_encoding() {
    let message = message::ResponseMessage { invocation_id: 0, body: mock_payload() };
    let reconstructed_message = message::ResponseMessage::decode(&message.clone().encode());
    assert_eq!(message, reconstructed_message);
}

#[derive(Default)]
struct MessageStore {
    inner: VecDeque<u8>,
}

impl Read for MessageStore {
    fn read_exact(&mut self, buf: &mut [u8]) -> anyhow::Result<()> {
        buf.fill_with(|| self.inner.pop_front().unwrap());
        Ok(())
    }
}

impl Write for MessageStore {
    fn write_all(&mut self, buf: &[u8]) -> anyhow::Result<()> {
        self.inner.reserve(buf.len());
        self.inner.extend(buf);
        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        Ok(())
    }
}

#[test]
fn test_invocation_channel() {
    let mut invocation_channel = InvocationChannel::new(Box::new(MessageStore::default()));

    let message = message::RequestMessage { invocation_id: 4, body: mock_payload() };

    invocation_channel.write_message(message.clone()).unwrap();

    let (reconstructed_message, _): (RequestMessage, _) =
        invocation_channel.read_message().unwrap();
    assert_eq!(message, reconstructed_message);
}

#[test]
fn test_invocation_channel_double_start_frame() {
    let mut invocation_channel = {
        let message = message::RequestMessage { invocation_id: 0, body: mock_payload() }.encode();
        let start_frame = frame::bytes_into_frames(&message).unwrap().first().unwrap().clone();
        let mut frame_store = frame::Framed::new(Box::new(MessageStore::default()));
        frame_store.write_frame(start_frame.clone()).unwrap();
        frame_store.write_frame(start_frame).unwrap();
        InvocationChannel { inner: frame_store }
    };

    invocation_channel.read_message::<message::RequestMessage>().unwrap_err();
}

#[test]
fn test_invocation_channel_expected_start_frame() {
    let mut invocation_channel = {
        let message = message::RequestMessage { invocation_id: 0, body: mock_payload() }.encode();
        let end_frame = frame::bytes_into_frames(&message).unwrap().last().unwrap().clone();
        let mut frame_store = frame::Framed::new(Box::new(MessageStore::default()));
        frame_store.write_frame(end_frame).unwrap();
        InvocationChannel { inner: frame_store }
    };

    invocation_channel.read_message::<message::RequestMessage>().unwrap_err();
}

#[test]
fn test_receive_raw_with_remainder() -> anyhow::Result<()> {
    let payload = mock_payload();

    let mut message_store = MessageStore::default();
    message_store.write_all(&(payload.len() as u32).to_le_bytes())?;
    message_store.write_all(&payload)?;
    assert_eq!(basic_framed::receive_raw(&mut message_store)?, payload);

    let mut acks = Vec::new();
    while message_store.inner.len() >= 4 {
        let mut ack: [u8; 4] = Default::default();
        message_store.read_exact(&mut ack)?;
        acks.push(u32::from_le_bytes(ack));
    }
    assert_eq!(message_store.inner.len(), 0);
    let mut expected_acks = vec![4096u32; payload.len() / 4096];
    expected_acks.push((payload.len() as u32) % 4096);
    assert_eq!(acks, expected_acks);

    Ok(())
}

#[test]
fn test_receive_raw_without_remainder() -> anyhow::Result<()> {
    let mut payload = mock_payload();
    payload.truncate((payload.len() / 4096) * 4096);

    let mut message_store = MessageStore::default();
    message_store.write_all(&(payload.len() as u32).to_le_bytes())?;
    message_store.write_all(&payload)?;
    assert_eq!(basic_framed::receive_raw(&mut message_store)?, payload);

    let mut acks = Vec::new();
    while message_store.inner.len() >= 4 {
        let mut ack: [u8; 4] = Default::default();
        message_store.read_exact(&mut ack)?;
        acks.push(u32::from_le_bytes(ack));
    }
    assert_eq!(message_store.inner.len(), 0);
    assert_eq!(acks, vec![4096u32; payload.len() / 4096]);

    Ok(())
}
