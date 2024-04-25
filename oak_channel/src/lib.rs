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
#![allow(rustdoc::private_intra_doc_links)]
#![feature(array_chunks)]

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "client")]
pub mod client;

pub mod basic_framed;
mod frame;
pub mod message;
pub mod server;

#[cfg(test)]
mod tests;

extern crate alloc;
use alloc::{boxed::Box, vec::Vec};

use anyhow::Context;
use bytes::BytesMut;
use oak_core::timer::Timer;

/// Simple no_std compatible equivalent of [`std::io::Read`].
///
/// [`std::io::Read`]: <https://doc.rust-lang.org/std/io/trait.Read.html>
pub trait Read {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Read> Read for T {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.read_exact(data).map_err(anyhow::Error::msg)
    }
}

/// Simple no_std compatible equivalent of [`std::io::Write`].
///
/// [`std::io::Write`]: <https://doc.rust-lang.org/std/io/trait.Write.html>
pub trait Write {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()>;
    fn flush(&mut self) -> anyhow::Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Write> Write for T {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
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
        Self { inner: frame::Framed::new(socket) }
    }

    pub fn read_message<M: message::Message>(&mut self) -> anyhow::Result<(M, Timer)> {
        // `message_buffer` will contain the full message we are going to read. Instead
        // of allocating separate buffers and copying data into
        // `message_buffer`, we will ensure that `message_buffer` has enough
        // capacity. There will be at least one frame, so we start with
        // the maximum size of a single frame body as initial capacity.
        let mut message_buffer = BytesMut::with_capacity(frame::MAX_BODY_SIZE);
        let (first_frame, timer) =
            self.inner.read_frame(&mut message_buffer).context("couldn't read frame")?;

        if !first_frame.flags.contains(frame::Flags::START) {
            anyhow::bail!("expected a frame with the START flag set");
        }

        if first_frame.flags.contains(frame::Flags::END) {
            return Ok((M::decode(&message_buffer[..]), timer));
        }

        // The length of the entire message is encoded in the body of the first frame.
        // The length includes the first frame. Decode it so the buffer needs to
        // be resized/copied at most once.
        let message_length: usize = {
            let mut buffer = [0u8; message::LENGTH_SIZE];
            let range = message::LENGTH_OFFSET..(message::LENGTH_OFFSET + message::LENGTH_SIZE);
            buffer.copy_from_slice(&first_frame.body[range]);
            usize::try_from(message::Length::from_le_bytes(buffer))
                .expect("couldn't convert message length to usize")
        };

        // This likely causes a copy of the pre-existing data, but we needed to read the
        // first frame to figure out how much space we need for the entire
        // message. No more resizes are going to happen from here.
        message_buffer.reserve(message_length - frame::MAX_BODY_SIZE);

        loop {
            let (frame, _) =
                self.inner.read_frame(&mut message_buffer).context("couldn't read frame")?;

            if frame.flags.contains(frame::Flags::START) {
                anyhow::bail!("received two frames with the START flag set");
            }

            if frame.flags.contains(frame::Flags::END) {
                break;
            }
        }

        Ok((M::decode(&message_buffer[..]), timer))
    }

    pub fn write_message<M: message::Message>(&mut self, message: M) -> anyhow::Result<()> {
        let encoded_data = message.encode();
        let frames: Vec<frame::Frame> = frame::bytes_into_frames(&encoded_data[..])?;
        for frame in frames.into_iter() {
            self.inner.write_frame(frame).context("couldn't write frame")?
        }
        Ok(())
    }
}
