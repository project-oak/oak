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

//! Wrappers for Oak SDK types to allow their use with std::io.

use crate::{channel_write, OakStatus};
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

/// Map an [`OakStatus`] value to the nearest available [`std::io::Result`].
fn result_from_status<T>(status: Option<OakStatus>, val: T) -> std::io::Result<T> {
    match status {
        Some(OakStatus::OAK_STATUS_UNSPECIFIED) => Err(io::Error::new(
            io::ErrorKind::Other,
            "Unspecified Oak status value",
        )),
        Some(OakStatus::OK) => Ok(val),
        Some(OakStatus::ERR_BAD_HANDLE) => {
            Err(io::Error::new(io::ErrorKind::NotConnected, "Bad handle"))
        }
        Some(OakStatus::ERR_INVALID_ARGS) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Invalid arguments",
        )),
        Some(OakStatus::ERR_CHANNEL_CLOSED) => Err(io::Error::new(
            io::ErrorKind::ConnectionReset,
            "Channel closed",
        )),
        Some(OakStatus::ERR_BUFFER_TOO_SMALL) => Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "Buffer too small",
        )),
        Some(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL) => Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "Handle space too small",
        )),
        Some(OakStatus::ERR_OUT_OF_RANGE) => {
            Err(io::Error::new(io::ErrorKind::NotConnected, "Out of range"))
        }
        Some(OakStatus::ERR_INTERNAL) => {
            Err(io::Error::new(io::ErrorKind::Other, "Internal error"))
        }
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
