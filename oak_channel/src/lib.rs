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

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(never_type)]
#![feature(unwrap_infallible)]
#![allow(rustdoc::private_intra_doc_links)]

#[cfg(feature = "client")]
pub mod client;

pub mod server;

mod frame;
mod message;

#[cfg(test)]
mod tests;

extern crate alloc;
use alloc::{boxed::Box, vec::Vec};
use anyhow::Context;

pub trait Read {
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Read> Read for T {
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.read_exact(data).map_err(anyhow::Error::msg)
    }
}

pub trait Write {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()>;
    fn flush(&mut self) -> anyhow::Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Write> Write for T {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.write_all(data).map_err(anyhow::Error::msg)
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        std::io::Write::flush(self).map_err(anyhow::Error::msg)
    }
}

pub trait Channel: Read + Write + Send + Sync {}

impl<T: Read + Write + Send + Sync> Channel for T {}

struct InvocationChannel {
    inner: frame::Framed,
}

impl InvocationChannel {
    pub fn new(socket: Box<dyn Channel>) -> Self {
        Self {
            inner: frame::Framed::new(socket),
        }
    }

    pub fn read_message<M: message::Message>(&mut self) -> anyhow::Result<M> {
        // `encoded_message` will contain the full message we are going to read. Instead of
        // allocating separate buffers and copying data into `encoded_message`, we will ensure that
        // `encoded_message` has enough space and pass mutable slices pointing into it to the
        // `read_frame` calls.
        let mut encoded_message: Vec<u8> = Vec::new();
        let first_frame = self
            .inner
            .read_frame(|new_len| {
                // encoded_message is initially empty, so we need to reserve space for the first
                // frame
                encoded_message.resize(new_len, 0);
                &mut encoded_message[..]
            })
            .context("couldn't read frame")?;
        let mut cursor = first_frame.body.len();

        if !first_frame.flags.contains(frame::Flags::START) {
            anyhow::bail!("expected a frame with the START flag set");
        }

        if first_frame.flags.contains(frame::Flags::END) {
            return Ok(M::decode(first_frame.body));
        }

        let message_length: usize = {
            let mut message_length_bytes = [0u8; message::LENGTH_SIZE];
            let message_length_offset = message::LENGTH_OFFSET;
            let message_length_range =
                message_length_offset..(message_length_offset + message::LENGTH_SIZE);
            message_length_bytes.copy_from_slice(&first_frame.body[message_length_range]);
            usize::try_from(message::Length::from_le_bytes(message_length_bytes))
                .expect("couldn't convert message length to usize")
        };

        // This *may* cause a copy of the pre-existing data, but we needed to read the first frame
        // to figure out how much space we need for the rest of it.
        encoded_message.resize(message_length, 0);

        // `cursor` will point to the starting point of the data for the next frame; each
        // iteration, we keep pusing it forward. As we're supposed to know the size of the
        // message, at the very end of the loop `cursor` should point to the end of the vector.
        loop {
            let frame = self
                .inner
                .read_frame(|len| &mut encoded_message[cursor..cursor + len])
                .context("couldn't read frame")?;
            cursor += frame.body.len();

            if frame.flags.contains(frame::Flags::START) {
                anyhow::bail!("received two frames with the START flag set");
            }

            if frame.flags.contains(frame::Flags::END) {
                break;
            }
        }
        if cursor != encoded_message.len() {
            anyhow::bail!("we received last frame before reading all of expected data");
        }

        Ok(M::decode(&encoded_message[..]))
    }

    pub fn write_message<M: message::Message>(&mut self, message: M) -> anyhow::Result<()> {
        let encoded_data = message.encode();
        let frames: Vec<frame::Frame> = frame::bytes_into_frames(&encoded_data[..])?;
        for frame in frames.into_iter() {
            self.inner
                .write_frame(frame)
                .context("couldn't write frame")?
        }
        Ok(())
    }
}
