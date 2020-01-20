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

use crate::OakStatus;
use std::io;

mod decodable;
mod encodable;
mod receiver;
mod sender;

pub use decodable::Decodable;
pub use encodable::Encodable;
pub use receiver::Receiver;
pub use sender::Sender;

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
        OakStatus::ERR_CHANNEL_EMPTY => {
            io::Error::new(io::ErrorKind::UnexpectedEof, "Channel empty")
        }
    }
}
