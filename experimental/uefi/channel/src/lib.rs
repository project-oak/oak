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

/// Length of the entire frame, including the header.
pub type FrameLength = u32;
const FRAME_BYTES_SIZE: usize = 4;

pub struct Frame {
    pub body: Vec<u8>,
}

pub struct Framed<T: Read + Write> {
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
            let mut length_bytes = [0; FRAME_BYTES_SIZE];
            self.inner.read_exact(&mut length_bytes)?;
            FrameLength::from_le_bytes(length_bytes)
        };

        let body = {
            let body_length: u32 = length - FRAME_BYTES_SIZE as u32;
            let mut body: Vec<u8> = vec![
                0;
                usize::try_from(body_length).expect(
                    "the supported pointer size is smaller than the frame length"
                )
            ];
            self.inner.read_exact(&mut body)?;
            body
        };

        Ok(Frame { body })
    }

    pub fn write_frame(&mut self, frame: Frame) -> anyhow::Result<()> {
        let length_bytes = {
            let length = FrameLength::try_from(FRAME_BYTES_SIZE + frame.body.len())
                .map_err(anyhow::Error::msg)
                .context("the frame is too large")?;
            length.to_le_bytes()
        };
        self.inner.write_all(&length_bytes)?;
        self.inner.write_all(&frame.body)?;
        Ok(())
    }
}
