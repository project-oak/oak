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
use anyhow::{bail, Context};
use oak_remote_attestation_sessions::{SessionId, SESSION_ID_LENGTH};

pub mod framing;
mod logger;
mod remote_attestation;
mod wasm;

/// Basic hardware abstraction layer for sending data.
pub trait Channel {
    fn send(&mut self, data: &[u8]) -> anyhow::Result<()>;
    fn recv(&mut self, data: &mut [u8]) -> anyhow::Result<()>;
}

pub type FrameLength = u16;
// The frame length is a u16, which is two bytes encoded.
pub const FRAME_LENGTH_ENCODED_SIZE: usize = 2;

pub struct Frame {
    pub body: Vec<u8>,
}

impl Frame {
    pub fn read_from_channel(channel: &mut dyn Channel) -> anyhow::Result<Self> {
        let mut length_buf = [0; FRAME_LENGTH_ENCODED_SIZE];
        channel.recv(&mut length_buf)?;
        let length = FrameLength::from_be_bytes(length_buf);
        let mut body: Vec<u8> = vec![0; length.into()];
        channel.recv(&mut body)?;
        Ok(Frame { body })
    }

    pub fn write_to_channel(self, channel: &mut dyn Channel) -> anyhow::Result<()> {
        let length: FrameLength = FrameLength::try_from(self.body.len())
            .map_err(anyhow::Error::msg)
            .context("the frame body is too large")?;
        let encoded_length = length.to_be_bytes();
        let mut encoded_frame: Vec<u8> = Vec::with_capacity(encoded_length.len() + self.body.len());
        encoded_frame.extend(encoded_length);
        encoded_frame.extend(self.body);
        channel.send(&encoded_frame)?;
        Ok(())
    }
}

pub struct SerializeableRequest {
    pub session_id: SessionId,
    pub body: Vec<u8>,
}

impl From<SerializeableRequest> for Vec<u8> {
    fn from(serializeable_request: SerializeableRequest) -> Vec<u8> {
        // The payload is the request's body prepended with the 8 byte session_id.
        // This takes adavantage of the session_id's fixed size to avoid needing
        // to use a key/value pair binary serialization protocol.
        let mut serialized_request: Vec<u8> = Vec::with_capacity(
            serializeable_request.session_id.len() + serializeable_request.body.len(),
        );

        serialized_request.extend(serializeable_request.session_id);
        serialized_request.extend(serializeable_request.body);

        serialized_request
    }
}

impl TryFrom<&[u8]> for SerializeableRequest {
    type Error = anyhow::Error;

    fn try_from(serialized_request: &[u8]) -> Result<Self, Self::Error> {
        if serialized_request.len() < SESSION_ID_LENGTH {
            bail!(
                "Message too short to contain a SessionId. The length of a SessionId
                is {} bytes, the message received contained only {} bytes",
                SESSION_ID_LENGTH,
                serialized_request.len()
            );
        }

        let (session_id_slice, request_body_slice) = serialized_request.split_at(SESSION_ID_LENGTH);

        let mut session_id: SessionId = [0; SESSION_ID_LENGTH];
        session_id.copy_from_slice(session_id_slice);
        let body = request_body_slice.to_vec();

        Ok(Self { session_id, body })
    }
}
