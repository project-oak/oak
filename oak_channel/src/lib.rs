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
use alloc::{boxed::Box, vec, vec::Vec};
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
        let first_frame = self.inner.read_frame().context("couldn't read frame")?;

        if !first_frame.flags.contains(frame::Flags::START) {
            anyhow::bail!("expected a frame with the START flag set");
        }

        if first_frame.flags.contains(frame::Flags::END) {
            return Ok(M::decode(&first_frame.body[..]));
        }

        let message_length: usize = {
            let mut message_length_bytes: [u8; message::LENGTH_SIZE] = [0; message::LENGTH_SIZE];
            let message_length_offset = message::LENGTH_OFFSET;
            let message_length_range =
                message_length_offset..(message_length_offset + message::LENGTH_SIZE);
            message_length_bytes.copy_from_slice(&first_frame.body[message_length_range]);
            usize::try_from(message::Length::from_le_bytes(message_length_bytes))
                .expect("couldn't convert message lemgth to usize")
        };

        let mut encoded_message: Box<[u8]> = vec![0; message_length].into_boxed_slice();
        encoded_message[..first_frame.body.len()].clone_from_slice(&first_frame.body);
        let mut cursor = first_frame.body.len();

        loop {
            let frame = self.inner.read_frame().context("couldn't read frame")?;

            if frame.flags.contains(frame::Flags::START) {
                anyhow::bail!("received two frames with the START flag set");
            }

            encoded_message[cursor..cursor + frame.body.len()].clone_from_slice(&frame.body);
            cursor += frame.body.len();

            if frame.flags.contains(frame::Flags::END) {
                break;
            }
        }

        Ok(M::decode(&encoded_message[..]))
    }

    pub fn write_message<M: message::Message>(&mut self, message: M) -> anyhow::Result<()> {
        let frames: Vec<frame::Frame> = frame::bytes_into_frames(&message.encode())?;
        for frame in frames.into_iter() {
            self.inner
                .write_frame(frame)
                .context("couldn't write frame")?
        }
        Ok(())
    }
}
