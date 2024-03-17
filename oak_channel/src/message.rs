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

//! Implements the message layer as defined in `/oak_channel/SPEC.md`.

use alloc::vec::Vec;

pub type Length = u32;
pub const LENGTH_SIZE: usize = 4;
pub const LENGTH_OFFSET: usize = 0;
static_assertions::assert_eq_size!([u8; LENGTH_SIZE], Length);

pub type InvocationId = u32;
pub const INVOCATION_ID_SIZE: usize = 4;
pub const INVOCATION_ID_OFFSET: usize = 4;
static_assertions::assert_eq_size!([u8; INVOCATION_ID_SIZE], InvocationId);

pub const BODY_OFFSET: usize = 8;

// messages never have a length of zero, since it always includes a fixed size
// header.
#[allow(clippy::len_without_is_empty)]
pub trait Message {
    fn len(&self) -> usize;
    fn encode(self) -> Vec<u8>;
    fn decode(frames: &[u8]) -> Self;
}

/// Rust implementation of the Request Message structure defined in
/// `/oak_channel/SPEC.md`
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RequestMessage {
    pub invocation_id: InvocationId,
    pub body: Vec<u8>,
}

impl Message for RequestMessage {
    fn len(&self) -> usize {
        LENGTH_SIZE + INVOCATION_ID_SIZE + self.body.len()
    }

    fn encode(self) -> Vec<u8> {
        let len = self.len();
        let mut message_bytes: Vec<u8> = Vec::with_capacity(len);

        let length: Length =
            len.try_into().expect("couldn't convert the message length usize to u32");

        message_bytes.extend_from_slice(&length.to_le_bytes());
        message_bytes.extend_from_slice(&self.invocation_id.to_le_bytes());
        message_bytes.extend_from_slice(&self.body);

        message_bytes
    }

    fn decode(encoded_message: &[u8]) -> Self {
        let invocation_id = {
            let mut invocation_id_bytes: [u8; INVOCATION_ID_SIZE] = [0; INVOCATION_ID_SIZE];
            invocation_id_bytes.copy_from_slice(
                &encoded_message[INVOCATION_ID_OFFSET..(INVOCATION_ID_OFFSET + INVOCATION_ID_SIZE)],
            );
            InvocationId::from_le_bytes(invocation_id_bytes)
        };
        // TODO(#2848): Avoid reallocating here by using slices + lifetimes, or
        // reference counting.
        let body: Vec<u8> = encoded_message[BODY_OFFSET..].into();

        Self { invocation_id, body }
    }
}

/// Rust implementation of the Response Message structure defined in
/// `/oak_channel/SPEC.md`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ResponseMessage {
    pub invocation_id: InvocationId,
    pub body: Vec<u8>,
}

impl Message for ResponseMessage {
    fn len(&self) -> usize {
        LENGTH_SIZE + INVOCATION_ID_SIZE + self.body.len()
    }

    fn encode(self) -> Vec<u8> {
        let len = self.len();
        let mut message_bytes: Vec<u8> = Vec::with_capacity(len);

        let length: Length =
            len.try_into().expect("couldn't convert the message length usize to u32");

        message_bytes.extend_from_slice(&length.to_le_bytes());
        message_bytes.extend_from_slice(&self.invocation_id.to_le_bytes());
        message_bytes.extend_from_slice(&self.body);

        message_bytes
    }

    fn decode(encoded_message: &[u8]) -> Self {
        let invocation_id = {
            let mut invocation_id_bytes: [u8; INVOCATION_ID_SIZE] = [0; INVOCATION_ID_SIZE];
            invocation_id_bytes.copy_from_slice(
                &encoded_message[INVOCATION_ID_OFFSET..(INVOCATION_ID_OFFSET + INVOCATION_ID_SIZE)],
            );
            InvocationId::from_le_bytes(invocation_id_bytes)
        };
        // TODO(#2848): Avoid reallocating here by using slices + lifetimes, or
        // reference counting.
        let body: Vec<u8> = encoded_message[BODY_OFFSET..].into();

        Self { invocation_id, body }
    }
}
