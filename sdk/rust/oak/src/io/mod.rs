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
use oak_abi::label::Label;
use std::io;

mod receiver;
mod sender;

pub use oak_io::{Decodable, Encodable, Message, Receiver, Sender};
pub use receiver::ReceiverExt;
pub use sender::SenderExt;

/// Create a new channel for transmission of `Encodable` and `Decodable` types.
pub fn channel_create<T: Encodable + Decodable>(
    label: &Label,
) -> Result<(Sender<T>, Receiver<T>), OakStatus> {
    let (wh, rh) = crate::channel_create(label)?;
    Ok((Sender::<T>::new(wh), Receiver::<T>::new(rh)))
}

/// Map a non-OK [`OakStatus`] value to the nearest available [`std::io::Error`].
///
/// Panics if passed an `OakStatus::Ok` value.
pub fn error_from_nonok_status(status: OakStatus) -> io::Error {
    match status {
        OakStatus::Unspecified => {
            io::Error::new(io::ErrorKind::Other, "Unspecified Oak status value")
        }
        OakStatus::Ok => panic!("OK status found"),
        OakStatus::ErrBadHandle => io::Error::new(io::ErrorKind::NotConnected, "Bad handle"),
        OakStatus::ErrInvalidArgs => {
            io::Error::new(io::ErrorKind::InvalidInput, "Invalid arguments")
        }
        OakStatus::ErrChannelClosed => {
            io::Error::new(io::ErrorKind::ConnectionReset, "Channel closed")
        }
        OakStatus::ErrBufferTooSmall => {
            io::Error::new(io::ErrorKind::UnexpectedEof, "Buffer too small")
        }
        OakStatus::ErrHandleSpaceTooSmall => {
            io::Error::new(io::ErrorKind::UnexpectedEof, "Handle space too small")
        }
        OakStatus::ErrOutOfRange => io::Error::new(io::ErrorKind::NotConnected, "Out of range"),
        OakStatus::ErrInternal => io::Error::new(io::ErrorKind::Other, "Internal error"),
        OakStatus::ErrTerminated => io::Error::new(io::ErrorKind::Other, "Node terminated"),
        OakStatus::ErrChannelEmpty => io::Error::new(io::ErrorKind::UnexpectedEof, "Channel empty"),
        OakStatus::ErrPermissionDenied => {
            io::Error::new(io::ErrorKind::PermissionDenied, "Permission denied")
        }
    }
}
