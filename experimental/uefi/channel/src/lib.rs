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

#![no_std]
#![feature(never_type)]

extern crate alloc;

use alloc::{vec, vec::Vec};
use anyhow::Context;
use ciborium_io::{Read, Write};
use core::assert;

/// Length of the entire frame, including the header.
pub type FrameLength = u32;
const FRAME_LENGTH_SIZE: usize = 4;
static_assertions::assert_eq_size!([u8; FRAME_LENGTH_SIZE], FrameLength);

/// Links multiple frames that make up a single message. Links request
/// messages with the respective response message.
pub type InvocationId = u16;
const INVOCATION_ID_SIZE: usize = 2;
static_assertions::assert_eq_size!([u8; INVOCATION_ID_SIZE], InvocationId);

/// TODO(#2848): Implement remaining header values.
pub const FRAME_HEADER_SIZE: usize = 6;
static_assertions::assert_eq_size!(
    [u8; FRAME_HEADER_SIZE],
    [u8; FRAME_LENGTH_SIZE + INVOCATION_ID_SIZE]
);

pub struct Frame {
    pub invocation_id: InvocationId,
    pub body: Vec<u8>,
}

impl Frame {
    /// Returns the size of the Frame encoded as bytes. On the wire each frame
    /// is prefixed with its length. Matching other framing formats such as
    /// UDP, this size includes all of the frame, including the length prefix.
    /// The length is intentionally not stored as a value in the frame struct
    /// itself, as this may lead to inconsistent information if other values
    /// values are mutated.
    fn wire_length(&self) -> anyhow::Result<FrameLength> {
        FrameLength::try_from(FRAME_LENGTH_SIZE + self.body.len())
            .map_err(anyhow::Error::msg)
            .context("the frame is too large")
    }
}

pub struct Framed<T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>> {
    inner: T,
}

impl<T> Framed<T>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    pub fn new(channel: T) -> Self {
        Self { inner: channel }
    }

    pub fn read_frame(&mut self) -> anyhow::Result<Frame> {
        let length = {
            let mut length_bytes = [0; FRAME_LENGTH_SIZE];
            self.inner.read_exact(&mut length_bytes)?;
            FrameLength::from_le_bytes(length_bytes)
        };
        let invocation_id = {
            let mut invocation_bytes = [0; INVOCATION_ID_SIZE];
            self.inner.read_exact(&mut invocation_bytes)?;
            InvocationId::from_le_bytes(invocation_bytes)
        };

        let body = {
            let body_length: u32 = length - FRAME_HEADER_SIZE as u32;
            let mut body: Vec<u8> = vec![
                0;
                usize::try_from(body_length).expect(
                    "the supported pointer size is smaller than the frame length"
                )
            ];
            self.inner.read_exact(&mut body)?;
            body
        };

        Ok(Frame {
            invocation_id,
            body,
        })
    }

    pub fn write_frame(&mut self, frame: Frame) -> anyhow::Result<()> {
        let length_bytes = frame.wire_length()?.to_le_bytes();
        self.inner.write_all(&length_bytes)?;
        let invocation_id_bytes = frame.invocation_id.to_le_bytes();
        self.inner.write_all(&invocation_id_bytes)?;
        self.inner.write_all(&frame.body)?;
        Ok(())
    }
}

pub struct ClientTransport<T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>> {
    inner: Framed<T>,
    next_invocation_id: InvocationId,
}

impl<T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>> ClientTransport<T> {
    pub fn new(channel: T) -> Self {
        let framed = Framed::new(channel);
        Self {
            inner: framed,
            next_invocation_id: 0,
        }
    }

    fn new_invocation_id(&mut self) -> InvocationId {
        let invocation_id = self.next_invocation_id;

        // TODO(#2848): Once fragmenting messages into multiple frames is
        // implemented there may be a set of pending invocations (for whom
        // there are outstanding frames to be sent / response frames to be
        // received). We must then handle the error case that occurs when
        // assigning a new invocation to the same ID.
        self.next_invocation_id = self.next_invocation_id.checked_add(1).unwrap_or(0);

        invocation_id
    }

    pub fn invoke(&mut self, req: Vec<u8>) -> anyhow::Result<Vec<u8>> {
        let invocation_id = self.new_invocation_id();
        self.inner.write_frame(Frame {
            invocation_id,
            body: req,
        })?;
        let response = self.inner.read_frame()?;

        // In the current implementation, messages are sent and received as
        // serialized single frames. We therefore assert that the response must
        // match the request frame. TODO(#2848): Update this to support
        // messages sent over multiple frames.
        assert!(response.invocation_id == invocation_id);

        Ok(response.body)
    }
}
