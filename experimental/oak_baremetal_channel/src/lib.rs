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
#![allow(rustdoc::private_intra_doc_links)]

pub mod client;
pub mod server;

#[cfg(test)]
mod tests;

extern crate alloc;

use crate::alloc::string::ToString;
use alloc::{string::String, vec, vec::Vec};
use anyhow::Context;
use ciborium_io::{Read, Write};

pub mod schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services.rs"));
}

/// Length of the entire frame, including the header.
type FrameLength = u32;
const FRAME_LENGTH_SIZE: usize = 4;
static_assertions::assert_eq_size!([u8; FRAME_LENGTH_SIZE], FrameLength);

/// In request frames this field contains the id of the method that is invoked.
/// In response frames this field contains the status code of the method invocation.
type MethodOrStatus = u32;
const METHOD_SIZE: usize = 4;
static_assertions::assert_eq_size!([u8; METHOD_SIZE], MethodOrStatus);

// TODO(#2848): Use this space to send a stream identifier that identifies
// frames as belonging to the same message. Currently the frames of every message
// must be sent as an uninterrupted seqeuence. A stream identifier would allow us
// to interleave messages.
/// Reserved space to maintain 8 byte alignement.
const PADDING_SIZE: usize = 4;

#[repr(u32)]
#[derive(Copy, Clone, strum::Display, strum::FromRepr)]
enum Flag {
    /// Atomic frame, a message sent as a single frame
    AtomicMessage = 0,
    /// Starts a stream of frames that constitute a message
    MessageStart = 1,
    /// Continues a stream of frames that constitute a message
    MessageContinuation = 2,
    /// Ends a stream of frames that constitute a message, indicating that the recipient may
    /// process the message.
    MessageMessage = 3,
}
const FLAG_SIZE: usize = 4;
static_assertions::assert_eq_size!([u8; FLAG_SIZE], Flag);
impl From<Flag> for [u8; FLAG_SIZE] {
    fn from(flag: Flag) -> Self {
        (flag as u32).to_le_bytes()
    }
}

const FRAME_HEADER_SIZE: usize = 16;
static_assertions::assert_eq_size!(
    [u8; FRAME_HEADER_SIZE],
    [u8; FRAME_LENGTH_SIZE + METHOD_SIZE + PADDING_SIZE + FLAG_SIZE]
);
// Ensure that the frame header is 8 Byte aligned.
static_assertions::const_assert!(FRAME_HEADER_SIZE % 8 == 0);

const MAX_FRAME_SIZE: usize = 64000;
const MAX_FRAME_BODY_SIZE: usize = MAX_FRAME_SIZE - FRAME_HEADER_SIZE;

/// A [`Frame`] is a small unit data that is sent over the communication
/// channel. Usually several [`Frame`]s are used to send a [`Message`].
#[derive(Clone)]
struct Frame {
    method_or_status: MethodOrStatus,
    flag: Flag,
    body: Vec<u8>,
}

impl Frame {
    /// Returns the size of the Frame encoded as bytes. On the wire each frame
    /// is prefixed with its length. This size includes all of the frame,
    /// including the length prefix. The length is intentionally not stored as a
    /// value in the frame struct itself, as this may lead to inconsistent
    /// information if other values are mutated.
    fn len(&self) -> anyhow::Result<FrameLength> {
        FrameLength::try_from(FRAME_HEADER_SIZE + self.body.len())
            .map_err(anyhow::Error::msg)
            .context("the frame is too large")
    }
}

impl TryFrom<Frame> for Vec<u8> {
    type Error = anyhow::Error;
    fn try_from(frame: Frame) -> Result<Self, Self::Error> {
        let frame_length = frame.len()?;
        let mut frame_bytes: Vec<u8> = Vec::with_capacity(
            frame_length
                .try_into()
                .map_err(|_| anyhow::Error::msg("Failed to convert usize into u32"))?,
        );

        let length_bytes = frame_length.to_le_bytes();
        frame_bytes.extend_from_slice(&length_bytes);
        let method_or_status_bytes = frame.method_or_status.to_le_bytes();
        frame_bytes.extend_from_slice(&method_or_status_bytes);
        let padding_bytes = [0; PADDING_SIZE];
        frame_bytes.extend_from_slice(&padding_bytes);
        let flag_bytes: [u8; FLAG_SIZE] = frame.flag.into();
        frame_bytes.extend_from_slice(&flag_bytes);
        frame_bytes.extend_from_slice(&frame.body);

        Ok(frame_bytes)
    }
}

/// A [`Message`] is conceptual unit of data that is sent over the communication
/// channel. It can represent either a full request, or full response of an oak_idl
/// invocation. Requests and responses can be converted to a [`Message`], and
/// vice versa. Usually a single [`Message`] is sent over the communication
/// channel over several [`Frame`]s.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Message {
    pub method_or_status: MethodOrStatus,
    pub body: Vec<u8>,
}

/// Deconstruct a [`Message`] into a set of [`Frame`]s.
impl From<Message> for Vec<Frame> {
    fn from(message: Message) -> Self {
        let frame_bodies: Vec<Vec<u8>> = if message.body.is_empty() {
            // Messages with an empty body are handled differently, since
            // chunking an empty [`Vec`] would result in 0 chunks.
            vec![vec![]]
        } else {
            message
                .body
                .chunks(MAX_FRAME_BODY_SIZE)
                // TODO(#2848): It'd be nice if we didn't have to reallocate here.
                // We may be able to avoid doing so by making [`Frame`] use
                // slices and lifetimes. Or alternatively use the Bytes crate for
                // reference counting.
                .map(|frame_body| frame_body.to_vec())
                .collect()
        };

        let number_of_frames = frame_bodies.len();
        frame_bodies
            .into_iter()
            .enumerate()
            .map(|(index, body)| {
                let flag = {
                    if index == 0 {
                        match number_of_frames {
                            1 => Flag::AtomicMessage,
                            _ => Flag::MessageStart,
                        }
                    } else if index == number_of_frames - 1 {
                        Flag::MessageMessage
                    } else {
                        Flag::MessageContinuation
                    }
                };
                Frame {
                    method_or_status: message.method_or_status,
                    flag,
                    body,
                }
            })
            .collect()
    }
}

/// Struct to incrementally build a [`Message`] from a set of [`Frame`]s.
#[derive(Default, Debug, PartialEq, Eq)]
struct PartialMessage {
    inner: Option<Message>,
}

#[derive(Debug, PartialEq, Eq, strum::Display)]
enum MessageReconstructionErrors {
    ExpectedStartFrame,
    DoubleStartFrame,
    MismatchingFrameHeader,
}

impl From<MessageReconstructionErrors> for anyhow::Error {
    fn from(error: MessageReconstructionErrors) -> Self {
        anyhow::Error::msg(error.to_string())
    }
}

#[derive(PartialEq, Eq, Debug)]
enum CompletionResult {
    Complete(Message),
    Incomplete(PartialMessage),
}

impl PartialMessage {
    /// Attempt to complete the [`PartialMessage`] with a frame. Returns
    /// an outer [`Result`] to handle errors resulting from invalid arguments.
    /// Returns an inner [`CompletionResult`] that contains either the succesfully
    /// completed message, or if more frames are needed to complete the message,
    /// a new [`PartialMessage`] that includes the previously passed frames.
    pub fn add_frame(self, frame: Frame) -> Result<CompletionResult, MessageReconstructionErrors> {
        match self.inner {
            None => match frame.flag {
                Flag::AtomicMessage => Ok(CompletionResult::Complete(Message {
                    method_or_status: frame.method_or_status,
                    body: frame.body,
                })),
                Flag::MessageStart => Ok(CompletionResult::Incomplete(Self {
                    inner: Some(Message {
                        method_or_status: frame.method_or_status,
                        body: frame.body,
                    }),
                })),
                _ => Err(MessageReconstructionErrors::ExpectedStartFrame),
            },
            Some(partial_message) => match frame.flag {
                Flag::MessageMessage => {
                    let new_partial_message =
                        PartialMessage::append_partial_message(partial_message, frame)?;
                    Ok(CompletionResult::Complete(new_partial_message))
                }
                Flag::MessageContinuation => {
                    let new_partial_message =
                        PartialMessage::append_partial_message(partial_message, frame)?;

                    Ok(CompletionResult::Incomplete(Self {
                        inner: Some(new_partial_message),
                    }))
                }
                _ => Err(MessageReconstructionErrors::DoubleStartFrame),
            },
        }
    }
    fn append_partial_message(
        mut partial_message: Message,
        mut frame: Frame,
    ) -> Result<Message, MessageReconstructionErrors> {
        if frame.method_or_status != partial_message.method_or_status {
            return Err(MessageReconstructionErrors::MismatchingFrameHeader);
        }
        partial_message.body.append(&mut frame.body);
        Ok(partial_message)
    }
}

/// Private struct used to send frames over an underlying channel.
struct Framed<T: Read + Write> {
    inner: T,
}

impl<T> Framed<T>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    pub fn new(socket: T) -> Self {
        Self { inner: socket }
    }

    pub fn read_frame(&mut self) -> anyhow::Result<Frame> {
        let length = {
            let mut length_bytes = [0; FRAME_LENGTH_SIZE];
            self.inner.read_exact(&mut length_bytes)?;
            FrameLength::from_le_bytes(length_bytes)
        };
        let method_or_status = {
            let mut method_or_status_bytes = [0; METHOD_SIZE];
            self.inner.read_exact(&mut method_or_status_bytes)?;
            MethodOrStatus::from_le_bytes(method_or_status_bytes)
        };
        let _padding_bytes = {
            let mut padding_bytes = [0; PADDING_SIZE];
            self.inner.read_exact(&mut padding_bytes)?;
            padding_bytes
        };
        let flag = {
            let mut method_or_status_bytes = [0; FLAG_SIZE];
            self.inner.read_exact(&mut method_or_status_bytes)?;
            Flag::from_repr(u32::from_le_bytes(method_or_status_bytes))
                .context("could not parse the frame header's flag field")?
        };

        let body = {
            let body_length: u32 = length - FRAME_HEADER_SIZE as u32;
            let mut body: Vec<u8> = vec![
                0;
                usize::try_from(body_length).expect(
                    "the supported pointer size is smaller than frame length"
                )
            ];
            self.inner.read_exact(&mut body)?;
            body
        };

        Ok(Frame {
            method_or_status,
            flag,
            body,
        })
    }

    pub fn write_frame(&mut self, frame: Frame) -> anyhow::Result<()> {
        let frame_bytes: Vec<u8> = frame.try_into()?;
        self.inner.write_all(&frame_bytes)?;
        self.inner.flush()?;
        Ok(())
    }
}

/// Public struct used to send and receive messages over an underlying channel.
struct InvocationChannel<T: Read + Write> {
    inner: Framed<T>,
}

impl<T> InvocationChannel<T>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    pub fn new(socket: T) -> Self {
        Self {
            inner: Framed::new(socket),
        }
    }
    fn recursively_complete_partial_message(
        &mut self,
        partial_message: PartialMessage,
    ) -> anyhow::Result<Message> {
        let frame = self.inner.read_frame()?;
        match partial_message.add_frame(frame)? {
            CompletionResult::Complete(message) => Ok(message),
            CompletionResult::Incomplete(partial_message) => {
                self.recursively_complete_partial_message(partial_message)
            }
        }
    }
    pub fn read_message(&mut self) -> anyhow::Result<Message> {
        self.recursively_complete_partial_message(PartialMessage::default())
    }
    pub fn write_message(&mut self, message: Message) -> anyhow::Result<()> {
        let frames: Vec<Frame> = message.into();
        for frame in frames.into_iter() {
            self.inner.write_frame(frame)?
        }
        Ok(())
    }
}
