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

use alloc::{
    collections::VecDeque,
    string::{String, ToString},
    vec,
};

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
fn test_invocation_channel_undersized_message_length() {
    // A peer sends a START frame (without END) whose declared total message
    // length is smaller than a single frame body. Reassembly must reject it
    // rather than underflowing the capacity reservation.
    let mut invocation_channel = {
        let mut body = vec![0u8; message::BODY_OFFSET];
        body[message::LENGTH_OFFSET..(message::LENGTH_OFFSET + message::LENGTH_SIZE)]
            .copy_from_slice(&(message::BODY_OFFSET as u32).to_le_bytes());
        let mut frame_store = frame::Framed::new(Box::new(MessageStore::default()));
        frame_store.write_frame(frame::Frame { flags: frame::Flags::START, body: &body }).unwrap();
        InvocationChannel { inner: frame_store }
    };

    invocation_channel.read_message::<message::RequestMessage>().unwrap_err();
}

#[test]
fn test_invocation_channel_truncated_first_frame() {
    // The first frame is too short to even contain the message length header.
    let mut invocation_channel = {
        let body = vec![0u8; message::LENGTH_SIZE - 1];
        let mut frame_store = frame::Framed::new(Box::new(MessageStore::default()));
        frame_store.write_frame(frame::Frame { flags: frame::Flags::START, body: &body }).unwrap();
        InvocationChannel { inner: frame_store }
    };

    invocation_channel.read_message::<message::RequestMessage>().unwrap_err();
}

#[test]
fn test_invocation_channel_undersized_single_frame() {
    // A single frame carrying the whole message (START and END both set) whose
    // body is shorter than the message header must be rejected rather than
    // panicking on the out-of-range header slice in decode.
    let mut invocation_channel = {
        let body = vec![0u8; message::BODY_OFFSET - 1];
        let mut frame_store = frame::Framed::new(Box::new(MessageStore::default()));
        frame_store
            .write_frame(frame::Frame {
                flags: frame::Flags::START | frame::Flags::END,
                body: &body,
            })
            .unwrap();
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

/// Builds a header with values `Frame::write` would never produce.
fn raw_header(padding: [u8; frame::PADDING_SIZE], length: u16, flags: u16) -> Vec<u8> {
    let mut header = Vec::with_capacity(frame::BODY_OFFSET);
    header.extend_from_slice(&padding);
    header.extend_from_slice(&length.to_le_bytes());
    header.extend_from_slice(&flags.to_le_bytes());
    header
}

fn encode_frame(flags: u16, body: &[u8]) -> Vec<u8> {
    let length = u16::try_from(frame::BODY_OFFSET + body.len()).unwrap();
    let mut frame = raw_header([0; frame::PADDING_SIZE], length, flags);
    frame.extend_from_slice(body);
    frame
}

fn read_frame_error(bytes: &[u8]) -> String {
    let mut store = MessageStore::default();
    store.write_all(bytes).unwrap();
    let mut framed = frame::Framed::new(Box::new(store));
    let mut message_buffer = BytesMut::new();
    framed.read_frame(&mut message_buffer).unwrap_err().to_string()
}

#[test]
fn test_read_frame_rejects_nonzero_padding() {
    let error = read_frame_error(&raw_header([0, 0, 1, 0], 16, frame::Flags::START.bits()));
    assert!(error.contains("desynchronised"), "{error}");
    assert!(error.contains("padding"), "{error}");
}

#[test]
fn test_read_frame_rejects_undefined_flags() {
    // START | END is 3, so 4 is the lowest bit the frame layer does not define.
    let error = read_frame_error(&raw_header([0; frame::PADDING_SIZE], 16, 4));
    assert!(error.contains("desynchronised"), "{error}");
    assert!(error.contains("flags"), "{error}");
}

#[test]
fn test_read_frame_rejects_a_length_that_leaves_no_body() {
    let length = u16::try_from(frame::BODY_OFFSET).unwrap();
    let error =
        read_frame_error(&raw_header([0; frame::PADDING_SIZE], length, frame::Flags::END.bits()));
    assert!(error.contains("desynchronised"), "{error}");
}

#[test]
fn test_read_frame_rejects_a_length_beyond_the_maximum() {
    let length = u16::try_from(frame::MAX_SIZE + 1).unwrap();
    let error =
        read_frame_error(&raw_header([0; frame::PADDING_SIZE], length, frame::Flags::END.bits()));
    assert!(error.contains("desynchronised"), "{error}");
}

#[test]
fn test_read_frame_rejects_a_stream_that_lost_bytes() {
    // What the header checks are for: a transport that discards part of a
    // write and still reports success.
    let body = vec![7u8; 64];
    let mut stream = encode_frame(frame::Flags::START.bits(), &body);
    stream.extend_from_slice(&encode_frame(frame::Flags::END.bits(), &body));
    let lost = 20..23;
    stream.drain(lost);

    let mut store = MessageStore::default();
    store.write_all(&stream).unwrap();
    let mut framed = frame::Framed::new(Box::new(store));

    // The first frame still parses: its header survived, so the reader trusts
    // the length and reads on into the second frame's header.
    let mut message_buffer = BytesMut::new();
    framed.read_frame(&mut message_buffer).unwrap();

    let mut message_buffer = BytesMut::new();
    let error = framed.read_frame(&mut message_buffer).unwrap_err().to_string();
    assert!(error.contains("desynchronised"), "{error}");
}
