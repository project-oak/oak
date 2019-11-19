//
// Copyright 2018 The Project Oak Authors
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

//! Wrappers for Oak SDK types to allow their use with [`std::io`].

use crate::{channel_close, channel_write, OakStatus};
#[cfg(test)]
use assert_matches::assert_matches;
use std::io;

/// Wrapper for a WriteHandle to implement the [`std::io::Write`] trait.
///
/// Methods taking `Write` trait objects require mutable references,
/// so use a distinct type rather than implementing the trait on the
/// base [`WriteHandle`] type.
///
/// [`WriteHandle`]: crate::WriteHandle
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Channel {
    handle: crate::WriteHandle,
}

impl Channel {
    /// Create a new `io::Channel` that uses the given channel handle.
    pub fn new(handle: crate::WriteHandle) -> Self {
        Channel { handle }
    }
    /// Close the underlying channel handle.
    pub fn close(self) -> std::io::Result<()> {
        result_from_status(Some(channel_close(self.handle.handle)), ())
    }
}

/// Implement the [`std::io::Write`] trait for `io::Channel`, to allow logging
/// and use of protobuf serialization methods.
impl std::io::Write for Channel {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let status = channel_write(self.handle, buf, &[]);
        result_from_status(Some(status), buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Map a non-OK [`OakStatus`] value to the nearest available [`std::io::Error`].
///
/// Panics if passed an `OakStatus::OK` value.
pub fn error_from_nonok_status(status: OakStatus) -> io::Error {
    match status {
        OakStatus::OAK_STATUS_UNSPECIFIED => {
            io::Error::new(io::ErrorKind::Other, "Unspecified Oak status value")
        }
        OakStatus::OK => panic!("OK status found"),
        OakStatus::ERR_BAD_HANDLE => io::Error::new(io::ErrorKind::NotConnected, "Bad handle"),
        OakStatus::ERR_INVALID_ARGS => {
            io::Error::new(io::ErrorKind::InvalidInput, "Invalid arguments")
        }
        OakStatus::ERR_CHANNEL_CLOSED => {
            io::Error::new(io::ErrorKind::ConnectionReset, "Channel closed")
        }
        OakStatus::ERR_BUFFER_TOO_SMALL => {
            io::Error::new(io::ErrorKind::UnexpectedEof, "Buffer too small")
        }
        OakStatus::ERR_HANDLE_SPACE_TOO_SMALL => {
            io::Error::new(io::ErrorKind::UnexpectedEof, "Handle space too small")
        }
        OakStatus::ERR_OUT_OF_RANGE => io::Error::new(io::ErrorKind::NotConnected, "Out of range"),
        OakStatus::ERR_INTERNAL => io::Error::new(io::ErrorKind::Other, "Internal error"),
        OakStatus::ERR_TERMINATED => io::Error::new(io::ErrorKind::Other, "Node terminated"),
    }
}

/// Map an [`OakStatus`] value to the nearest available [`std::io::Result`].
fn result_from_status<T>(status: Option<OakStatus>, val: T) -> std::io::Result<T> {
    match status {
        Some(OakStatus::OK) => Ok(val),
        Some(status) => Err(error_from_nonok_status(status)),
        None => Err(io::Error::new(
            io::ErrorKind::Other,
            "Unknown Oak status value",
        )),
    }
}

#[test]
fn test_result_from_status() {
    assert_matches!(result_from_status(Some(OakStatus::OK), 12), Ok(12));
    assert_matches!(result_from_status(None, 12), Err(_));
}
