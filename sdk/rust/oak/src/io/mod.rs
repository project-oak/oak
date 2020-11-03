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

/// Creates a new channel for transmission of [`Encodable`] and [`Decodable`] types.
pub fn channel_create<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
) -> Result<(Sender<T>, Receiver<T>), OakStatus> {
    let (wh, rh) = crate::channel_create(name, label)?;
    Ok((Sender::<T>::new(wh), Receiver::<T>::new(rh)))
}

/// Creates a node and corresponding inbound channel of the same type, and returns [`Sender`] for
/// such channel.
pub fn node_create<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
    node_config: &crate::NodeConfiguration,
) -> Result<Sender<T>, OakStatus> {
    let (sender, receiver) = channel_create(&format!("{}-in", name), label)?;
    crate::node_create(name, node_config, label, receiver.handle)?;
    receiver.close()?;
    Ok(sender)
}

/// Creates a node and corresponding inbound channel of the same type, for nodes that are
/// instantiated via the [`crate::entrypoint_command_handler`] macro.
pub fn entrypoint_node_create<T: crate::WasmEntrypoint>(
    name: &str,
    label: &Label,
    wasm_module_name: &str,
) -> Result<Sender<T::Message>, OakStatus> {
    let node_config = &crate::node_config::wasm(wasm_module_name, T::ENTRYPOINT_NAME);
    node_create(name, label, node_config)
}

/// Sends an init message over the provided [`Sender`], which is consumed by this method, and
/// returns a [`Sender`] for subsequent commands.
///
/// Useful for sending initial data to nodes instantiated via the
/// [`crate::entrypoint_command_handler_init`] macro.
pub fn send_init<Init: Encodable + Decodable, Command: Encodable + Decodable>(
    sender: Sender<oak_io::InitWrapper<Init, Command>>,
    init: Init,
    command_channel_label: &Label,
) -> Result<Sender<Command>, oak_io::OakError> {
    let (command_sender, command_receiver) =
        channel_create::<Command>("command sender", command_channel_label)?;
    let init_wrapper = oak_io::InitWrapper {
        init,
        command_receiver,
    };
    sender.send(&init_wrapper)?;
    Ok(command_sender)
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
