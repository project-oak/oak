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

extern crate alloc;

use alloc::{format, vec, vec::Vec};
use bitflags::bitflags;
use ciborium_io::{Read, Write};

pub const PADDING_SIZE: usize = 4;

type Length = u16;
pub const LENGTH_SIZE: usize = 2;
static_assertions::assert_eq_size!([u8; LENGTH_SIZE], Length);

bitflags! {
    #[derive(Default)]
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

pub const MAX_SIZE: usize = 64000;
pub const MAX_BODY_SIZE: usize = MAX_SIZE - BODY_OFFSET;

#[derive(Clone, Default, Debug)]
pub struct Frame {
    pub flags: Flags,
    pub body: Vec<u8>,
}

impl Frame {
    fn len(&self) -> anyhow::Result<Length> {
        let length = BODY_OFFSET + self.body.len();

        if length > MAX_SIZE {
            return Err(anyhow::Error::msg("frame exceeds the maximum frame size"));
        };

        Length::try_from(length).map_err(|_error| {
            anyhow::Error::msg(format!(
                "could convert the frame length usize to {:?}",
                core::any::type_name::<Length>()
            ))
        })
    }
}

impl TryFrom<Frame> for Vec<u8> {
    type Error = anyhow::Error;
    fn try_from(frame: Frame) -> Result<Self, Self::Error> {
        let frame_length = frame.len()?;
        let mut frame_bytes: Vec<u8> = Vec::with_capacity(frame_length.into());

        frame_bytes.extend_from_slice(&[0; PADDING_SIZE]);
        frame_bytes.extend_from_slice(&frame_length.to_le_bytes());
        frame_bytes.extend_from_slice(&frame.flags.bits.to_le_bytes());
        frame_bytes.extend_from_slice(&frame.body);

        Ok(frame_bytes)
    }
}

pub struct Framed<T: Read + Write> {
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
        let _padding = {
            let mut padding_bytes = [0; PADDING_SIZE];
            self.inner.read_exact(&mut padding_bytes)?;
            padding_bytes
        };
        let length: usize = {
            let mut length_bytes = [0; LENGTH_SIZE];
            self.inner.read_exact(&mut length_bytes)?;
            let length = Length::from_le_bytes(length_bytes).into();
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
            let body_length: usize = length - BODY_OFFSET;
            let mut body: Vec<u8> = vec![0; body_length];
            self.inner.read_exact(&mut body)?;
            body
        };

        Ok(Frame { flags, body })
    }

    pub fn write_frame(&mut self, frame: Frame) -> anyhow::Result<()> {
        let frame_bytes: Vec<u8> = frame.try_into()?;
        self.inner.write_all(&frame_bytes)?;
        self.inner.flush()?;
        Ok(())
    }
}

pub fn bytes_into_frames(data: Vec<u8>) -> Vec<Frame> {
    let mut frames: Vec<Frame> = data
        .chunks(MAX_BODY_SIZE)
        // TODO(#2848): It'd be nice if we didn't have to reallocate here.
        // We may be able to avoid doing so by making [`Frame`] use
        // slices and lifetimes. Or alternatively use the Bytes crate for
        // reference counting.
        .map(|frame_body| Frame {
            flags: Flags::default(),
            body: frame_body.to_vec(),
        })
        .collect();

    frames.first_mut().map(|frame| {
        frame.flags.set(Flags::START, true);
        Some(())
    });

    frames.last_mut().map(|frame| {
        frame.flags.set(Flags::END, true);
        Some(())
    });

    frames
}
