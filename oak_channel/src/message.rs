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

pub type MethodId = u32;
pub const METHOD_ID_SIZE: usize = 4;
pub const METHOD_ID_OFFSET: usize = 8;
static_assertions::assert_eq_size!([u8; METHOD_ID_SIZE], MethodId);

pub type StatusCode = u32;
pub const STATUS_CODE_SIZE: usize = 4;
pub const STATUS_CODE_OFFSET: usize = 8;
static_assertions::assert_eq_size!([u8; STATUS_CODE_SIZE], StatusCode);

pub const PADDING_SIZE: usize = 4;

pub const BODY_OFFSET: usize = 16;

pub trait Message {
    fn len(&self) -> usize;
    fn encode(self) -> Vec<u8>;
    fn decode(frames: Vec<u8>) -> Self;
}

/// Rust implementation of the Request Message structure defined in
/// `/oak_channel/SPEC.md`
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RequestMessage {
    pub invocation_id: InvocationId,
    // TODO(#3385): Remove this field when the protobuf IDL is used everywhere, since the method id
    // will then be part of the request body from the point of view of this struct.
    pub method_id: MethodId,
    pub body: Vec<u8>,
}

impl Message for RequestMessage {
    fn len(&self) -> usize {
        LENGTH_SIZE + INVOCATION_ID_SIZE + METHOD_ID_SIZE + PADDING_SIZE + self.body.len()
    }

    fn encode(self) -> Vec<u8> {
        let len = self.len();
        let mut message_bytes: Vec<u8> = Vec::with_capacity(len);

        let length: Length = len
            .try_into()
            .expect("could convert the message length usize to u32");

        message_bytes.extend_from_slice(&length.to_le_bytes());
        message_bytes.extend_from_slice(&self.invocation_id.to_le_bytes());
        message_bytes.extend_from_slice(&self.method_id.to_le_bytes());
        message_bytes.extend_from_slice(&[0; PADDING_SIZE]);
        message_bytes.extend_from_slice(&self.body);

        message_bytes
    }

    fn decode(mut encoded_message: Vec<u8>) -> Self {
        let invocation_id = {
            let mut invocation_id_bytes: [u8; INVOCATION_ID_SIZE] = [0; INVOCATION_ID_SIZE];
            invocation_id_bytes.copy_from_slice(
                &encoded_message[INVOCATION_ID_OFFSET..(INVOCATION_ID_OFFSET + INVOCATION_ID_SIZE)],
            );
            InvocationId::from_le_bytes(invocation_id_bytes)
        };
        let method_id = {
            let mut method_id_bytes: [u8; METHOD_ID_SIZE] = [0; METHOD_ID_SIZE];
            method_id_bytes.copy_from_slice(
                &encoded_message[METHOD_ID_OFFSET..(METHOD_ID_OFFSET + METHOD_ID_SIZE)],
            );
            MethodId::from_le_bytes(method_id_bytes)
        };
        // TODO(#2848): Avoid reallocating here by using slices + lifetimes, or
        // reference counting.
        let body: Vec<u8> = encoded_message.drain(BODY_OFFSET..).collect();

        Self {
            invocation_id,
            method_id,
            body,
        }
    }
}

/// Rust implementation of the Response Message structure defined in
/// `/oak_channel/SPEC.md`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ResponseMessage {
    pub invocation_id: InvocationId,
    pub status_code: StatusCode,
    pub body: Vec<u8>,
}

impl Message for ResponseMessage {
    fn len(&self) -> usize {
        LENGTH_SIZE + INVOCATION_ID_SIZE + STATUS_CODE_SIZE + PADDING_SIZE + self.body.len()
    }

    fn encode(self) -> Vec<u8> {
        let len = self.len();
        let mut message_bytes: Vec<u8> = Vec::with_capacity(len);

        let length: Length = len
            .try_into()
            .expect("could convert the message length usize to u32");

        message_bytes.extend_from_slice(&length.to_le_bytes());
        message_bytes.extend_from_slice(&self.invocation_id.to_le_bytes());
        message_bytes.extend_from_slice(&self.status_code.to_le_bytes());
        message_bytes.extend_from_slice(&[0; PADDING_SIZE]);
        message_bytes.extend_from_slice(&self.body);

        message_bytes
    }

    fn decode(mut encoded_message: Vec<u8>) -> Self {
        let invocation_id = {
            let mut invocation_id_bytes: [u8; INVOCATION_ID_SIZE] = [0; INVOCATION_ID_SIZE];
            invocation_id_bytes.copy_from_slice(
                &encoded_message[INVOCATION_ID_OFFSET..(INVOCATION_ID_OFFSET + INVOCATION_ID_SIZE)],
            );
            InvocationId::from_le_bytes(invocation_id_bytes)
        };
        let status_code = {
            let mut status_code_bytes: [u8; STATUS_CODE_SIZE] = [0; STATUS_CODE_SIZE];
            status_code_bytes.copy_from_slice(
                &encoded_message[STATUS_CODE_OFFSET..(STATUS_CODE_OFFSET + STATUS_CODE_SIZE)],
            );
            StatusCode::from_le_bytes(status_code_bytes)
        };
        // TODO(#2848): Avoid reallocating here by using slices + lifetimes, or
        // reference counting.
        let body: Vec<u8> = encoded_message.drain(BODY_OFFSET..).collect();

        Self {
            invocation_id,
            status_code,
            body,
        }
    }
}
