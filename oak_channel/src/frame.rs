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

//! Implements the frame layer as defined in `/oak_channel/SPEC.md`.

extern crate alloc;

use alloc::{boxed::Box, format, vec::Vec};
use core::borrow::BorrowMut;

use bitflags::bitflags;
use bytes::{BufMut, BytesMut};
use oak_core::timer::Timer;

use crate::Channel;

pub const PADDING_SIZE: usize = 4;

type Length = u16;
pub const LENGTH_SIZE: usize = 2;
static_assertions::assert_eq_size!([u8; LENGTH_SIZE], Length);

bitflags! {
    #[derive(Clone, Debug, Default)]
    pub struct Flags: u16 {
        const START = 1;
        const END = 2;
    }
}
pub const FLAGS_SIZE: usize = 2;
static_assertions::assert_eq_size!([u8; FLAGS_SIZE], Flags);

pub const BODY_OFFSET: usize = 8;
static_assertions::assert_eq_size!(
    [u8; BODY_OFFSET],
    [u8; PADDING_SIZE + LENGTH_SIZE + FLAGS_SIZE]
);
static PADDING: &[u8] = &[0; PADDING_SIZE];

// The maximum size of a frame, in bytes.
pub const MAX_SIZE: usize = 4000;
pub const MAX_BODY_SIZE: usize = MAX_SIZE - BODY_OFFSET;

/// Rust implementation of the Frame structure defined in
/// `/oak_channel/SPEC.md`.
#[derive(Clone, Default, Debug)]
pub struct Frame<'a> {
    pub flags: Flags,
    pub body: &'a [u8],
}

impl Frame<'_> {
    fn write<C: Channel + ?Sized>(&self, channel: &mut C) -> Result<(), anyhow::Error> {
        let frame_length = {
            let length = BODY_OFFSET.checked_add(self.body.len()).expect("body length overflow");
            Length::try_from(length).map_err(|_error| {
                anyhow::Error::msg(format!(
                    "could convert the frame length usize to {:?}",
                    core::any::type_name::<Length>()
                ))
            })?
        };
        channel.write_all(PADDING)?;
        channel.write_all(&frame_length.to_le_bytes())?;
        channel.write_all(&self.flags.bits().to_le_bytes())?;
        channel.write_all(self.body)?;
        Ok(())
    }
}

pub struct Framed {
    inner: Box<dyn Channel>,
}

impl Framed {
    pub fn new(socket: Box<dyn Channel>) -> Self {
        Self { inner: socket }
    }

    pub fn read_frame<'a>(
        &mut self,
        message_buffer: &'a mut BytesMut,
    ) -> anyhow::Result<(Frame<'a>, Timer)> {
        {
            let mut padding_bytes = [0; PADDING_SIZE];
            self.inner.read_exact(&mut padding_bytes)?;
        };
        // As the read() above can block indefinitely we'll start measuring the time it
        // took to read the data _after_ we've read the padding bytes. Strictly
        // speaking we should start measuring the time as we're reading the
        // first padding byte, but this should be close enough to get a rough
        // idea.
        let timer = Timer::new_rdtsc();
        let length: usize = {
            let mut length_bytes = [0; LENGTH_SIZE];
            self.inner.read_exact(&mut length_bytes)?;
            let length = Length::from_le_bytes(length_bytes).into();
            if length <= BODY_OFFSET {
                return Err(anyhow::Error::msg("frame is too small"));
            };
            if length > MAX_SIZE {
                return Err(anyhow::Error::msg("frame exceeds the maximum frame size"));
            };
            length
        };
        let flags = {
            let mut flags_bytes = [0; FLAGS_SIZE];
            self.inner.read_exact(&mut flags_bytes)?;
            Flags::from_bits_truncate(u16::from_le_bytes(flags_bytes))
        };

        let body = {
            let body_length: usize =
                length.checked_sub(BODY_OFFSET).expect("body length underflow");
            let tail = message_buffer.len();
            // Lack of capacity indicates corrupted frames and causes panic.
            message_buffer.put_bytes(0x00, body_length);
            self.inner.read_exact(&mut message_buffer[tail..])?;
            &message_buffer[tail..]
        };

        Ok((Frame { flags, body }, timer))
    }

    pub fn write_frame(&mut self, frame: Frame) -> anyhow::Result<()> {
        let channel: &mut dyn Channel = self.inner.borrow_mut();
        frame.write(channel)?;
        channel.flush()
    }
}

pub fn bytes_into_frames(data: &[u8]) -> anyhow::Result<Vec<Frame<'_>>> {
    if data.is_empty() {
        anyhow::bail!("cannot convert empty payloads into frames")
    }

    let mut frames: Vec<Frame> = data
        .chunks(MAX_BODY_SIZE)
        .map(|frame_body| Frame { flags: Flags::default(), body: frame_body })
        .collect();

    frames
        .first_mut()
        .expect("there should always be at least one frame")
        .flags
        .set(Flags::START, true);

    frames
        .last_mut()
        .expect("there should always be at least one frame")
        .flags
        .set(Flags::END, true);

    Ok(frames)
}
