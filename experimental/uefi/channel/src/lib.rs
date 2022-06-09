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
pub type FrameLength = u32;
const FRAME_LENGTH_SIZE: usize = 4;
static_assertions::assert_eq_size!([u8; FRAME_LENGTH_SIZE], FrameLength);

/// In request frames this field contains the id of the method_or_status that is invoked.
/// In response frames this field contains the status code of the method_or_status invocation.
pub type Method = u32;
const METHOD_SIZE: usize = 4;
static_assertions::assert_eq_size!([u8; METHOD_SIZE], Method);

pub const FRAME_HEADER_SIZE: usize = 8;
static_assertions::assert_eq_size!(
    [u8; FRAME_HEADER_SIZE],
    [u8; FRAME_LENGTH_SIZE + METHOD_SIZE]
);

pub struct Frame {
    pub method_or_status: Method,
    pub body: Vec<u8>,
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
            let mut length_bytes = [0; FRAME_LENGTH_SIZE];
            self.inner.read_exact(&mut length_bytes)?;
            FrameLength::from_le_bytes(length_bytes)
        };
        let method_or_status = {
            let mut method_or_status_bytes = [0; METHOD_SIZE];
            self.inner.read_exact(&mut method_or_status_bytes)?;
            Method::from_le_bytes(method_or_status_bytes)
        };

        let body = {
            let body_length: u32 = length - FRAME_HEADER_SIZE as u32;
            let mut body: Vec<u8> = vec![
                0;
                usize::try_from(body_length).expect(
                    "the supported pointer size is smaller than the frame length"
                )
            ];
            self.inner.read_exact(&mut body)?;
            body
        };

        Ok(Frame {
            method_or_status,
            body,
        })
    }

    pub fn write_frame(&mut self, frame: Frame) -> anyhow::Result<()> {
        let length_bytes = frame.len()?.to_le_bytes();
        self.inner.write_all(&length_bytes)?;
        let method_or_status_bytes = frame.method_or_status.to_le_bytes();
        self.inner.write_all(&method_or_status_bytes)?;
        self.inner.write_all(&frame.body)?;
        self.inner.flush()?;
        Ok(())
    }
}

impl<'a> From<oak_idl::Request<'a>> for Frame {
    fn from(request: oak_idl::Request) -> Frame {
        Frame {
            method_or_status: request.method_id,
            body: request.body.to_vec(),
        }
    }
}

impl<'a> From<&'a Frame> for oak_idl::Request<'a> {
    fn from(frame: &'a Frame) -> Self {
        oak_idl::Request {
            method_id: frame.method_or_status,
            body: &frame.body,
        }
    }
}

impl From<Result<Vec<u8>, oak_idl::Error>> for Frame {
    fn from(result: Result<Vec<u8>, oak_idl::Error>) -> Frame {
        // In response frames, the status code `0` indicates a succesful
        // response. Values above `0` represent an error code as defined
        // in the oak_idl.
        match result {
            Ok(response) => Frame {
                method_or_status: 0,
                body: response,
            },
            Err(error) => Frame {
                method_or_status: error.code.into(),
                body: error.message.as_bytes().to_vec(),
            },
        }
    }
}

impl From<Frame> for Result<Vec<u8>, oak_idl::Error> {
    fn from(frame: Frame) -> Self {
        // In response frames, the status code `0` indicates a succesful
        // response. Values above `0` represent an error code as defined
        // in the oak_idl.
        match frame.method_or_status {
            0 => Ok(frame.body),
            _ => Err(oak_idl::Error {
                code: frame.method_or_status.into(),
                message: String::from_utf8(frame.body).unwrap_or_else(|err| {
                    alloc::format!(
                        "Could not parse response error message bytes as utf8: {:?}",
                        err
                    )
                }),
            }),
        }
    }
}
