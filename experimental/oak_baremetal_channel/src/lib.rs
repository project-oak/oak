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

pub mod schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_servers.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_clients.rs"));
}

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

pub trait Write {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()>;
    fn flush(&mut self) -> anyhow::Result<()>;
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
        let mut encoded_message: Vec<u8> = Vec::new();
        let mut first_frame = self.inner.read_frame().context("failed to read frame.")?;

        if first_frame.flags.contains(frame::Flags::START) {
            if first_frame.flags.contains(frame::Flags::END) {
                return Ok(M::decode(first_frame.body));
            } else {
                let required_additional_capacity_to_hold_message = {
                    let message_length: usize = {
                        let mut message_length_bytes: [u8; message::LENGTH_SIZE] =
                            [0; message::LENGTH_SIZE];
                        let message_length_offset = frame::BODY_OFFSET + message::LENGTH_OFFSET;
                        let message_length_range =
                            message_length_offset..(message_length_offset + message::LENGTH_SIZE);
                        message_length_bytes
                            .copy_from_slice(&first_frame.body[message_length_range]);
                        usize::try_from(message::Length::from_le_bytes(message_length_bytes))
                            .expect("couldn't convert message lemgth to usize")
                    };
                    message_length - encoded_message.capacity()
                };
                if required_additional_capacity_to_hold_message > 0 {
                    encoded_message.reserve_exact(required_additional_capacity_to_hold_message);
                }

                encoded_message.append(&mut first_frame.body);
            }
        } else {
            anyhow::bail!("expected a frame with the START flag set.");
        }

        loop {
            let mut frame = self.inner.read_frame().context("failed to read frame.")?;

            if frame.flags.contains(frame::Flags::START) {
                anyhow::bail!("received two frames with the START flag set.");
            } else {
                encoded_message.append(&mut frame.body);
                if frame.flags.contains(frame::Flags::END) {
                    break;
                }
            };
        }

        Ok(M::decode(encoded_message))
    }

    pub fn write_message<M: message::Message>(&mut self, message: M) -> anyhow::Result<()> {
        let frames: Vec<frame::Frame> = frame::bytes_into_frames(message.encode())?;
        for frame in frames.into_iter() {
            self.inner
                .write_frame(frame)
                .context("failed to write frame.")?
        }
        Ok(())
    }
}
