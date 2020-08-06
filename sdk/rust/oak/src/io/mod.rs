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

use crate::{ChannelReadStatus, OakError, OakStatus};
use log::error;
use oak_abi::label::Label;
use std::io;

mod decodable;
mod encodable;
mod receiver;
mod sender;

pub use decodable::Decodable;
pub use encodable::Encodable;
pub use receiver::Receiver;
pub use sender::Sender;

/// Create a new channel for transmission of `Encodable` and `Decodable` types.
pub fn channel_create<T: Encodable + Decodable>() -> Result<(Sender<T>, Receiver<T>), OakStatus> {
    let (wh, rh) = crate::channel_create()?;
    Ok((Sender::<T>::new(wh), Receiver::<T>::new(rh)))
}

pub fn channel_create_with_label<T: Encodable + Decodable>(
    label: &Label,
) -> Result<(Sender<T>, Receiver<T>), OakStatus> {
    let (wh, rh) = crate::channel_create_with_label(label)?;
    Ok((Sender::<T>::new(wh), Receiver::<T>::new(rh)))
}

/// A simple holder for bytes + handles, using internally owned buffers.
#[derive(Debug, PartialEq, Eq)]
pub struct Message {
    pub bytes: Vec<u8>,
    pub handles: Vec<crate::Handle>,
}

/// Close the underlying channel used by the sender.
pub fn close_sender<T: Encodable>(sender: &Sender<T>) -> Result<(), OakStatus> {
    crate::channel_close(sender.handle.handle)
}

/// Attempt to send a value on the sender.
pub fn send<T: Encodable>(sender: &Sender<T>, t: &T) -> Result<(), OakError> {
    let message = t.encode()?;
    crate::channel_write(sender.handle, &message.bytes, &message.handles)?;
    Ok(())
}

/// Close the underlying channel used by the receiver.
pub fn close_receiver<T: Decodable>(receiver: &Receiver<T>) -> Result<(), OakStatus> {
    crate::channel_close(receiver.handle.handle)
}

/// Attempt to wait for a value on the receiver, blocking if necessary.
pub fn receive<T: Decodable>(receiver: &Receiver<T>) -> Result<T, OakError> {
    wait(receiver)?;
    try_receive(receiver)
}

/// Attempt to read a value from the receiver, without blocking.
pub fn try_receive<T: Decodable>(receiver: &Receiver<T>) -> Result<T, OakError> {
    let mut bytes = Vec::with_capacity(1024);
    let mut handles = Vec::with_capacity(16);
    crate::channel_read(receiver.handle, &mut bytes, &mut handles)?;
    // `bytes` and `handles` are moved into `Message`, so there is no extra copy happening here.
    let message = crate::io::Message { bytes, handles };
    T::decode(&message)
}

/// Wait for a value to be available from the receiver.
///
/// Returns [`ChannelReadStatus`] of the wrapped handle, or `Err(OakStatus::ErrTerminated)` if
/// the Oak Runtime is terminating.
pub fn wait<T: Decodable>(receiver: &Receiver<T>) -> Result<ChannelReadStatus, OakStatus> {
    // TODO(#500): Consider creating the handle notification space once and for all in `new`.
    let read_handles = vec![receiver.handle];
    let mut space = crate::new_handle_space(&read_handles);
    crate::prep_handle_space(&mut space);
    let status =
        unsafe { oak_abi::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32) };

    match crate::result_from_status(status as i32, ()) {
        Ok(()) => space
            .get(oak_abi::SPACE_BYTES_PER_HANDLE - 1)
            .cloned()
            .map(i32::from)
            .and_then(ChannelReadStatus::from_i32)
            .ok_or_else(|| {
                error!(
                    "Should never get here. `wait_on_channels` always yields a valid `ChannelReadStatus` if the returned status is not Err(OakStatus::ErrTerminated)."
                );
                OakStatus::ErrInternal
            }),
        Err(OakStatus::ErrTerminated) => Err(OakStatus::ErrTerminated),
        Err(OakStatus::ErrInvalidArgs) => {
            error!("Should never get here. `ErrInvalidArgs` here indicates that `space` is corrupted.");
            Err(OakStatus::ErrInternal)
        }
        Err(status) => {
            error!("Should never get here. `wait_on_channels` should never return {:?}.", status);
            Err(OakStatus::ErrInternal)
        }
    }
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
