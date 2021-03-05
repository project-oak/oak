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
use anyhow::Context;
use core::borrow::Borrow;
use oak_abi::label::Label;
use oak_services::proto::google::rpc;
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

/// Uses the current node's label-downgrading privilege to create a new channel for transmission of
/// [`Encodable`] and [`Decodable`] types.
pub fn channel_create_with_downgrade<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
) -> Result<(Sender<T>, Receiver<T>), OakStatus> {
    let (wh, rh) = crate::channel_create_with_downgrade(name, label)?;
    Ok((Sender::<T>::new(wh), Receiver::<T>::new(rh)))
}

/// Creates a node and corresponding inbound channel of the same type, and returns [`Sender`] for
/// such channel.
#[cfg(not(feature = "linear-handles"))] // no linear handles version
pub fn node_create<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
    node_config: &crate::NodeConfiguration,
) -> Result<Sender<T>, OakStatus> {
    let (sender, receiver) = channel_create(&format!("{}-in", name), label)?;
    match crate::node_create(name, node_config, label, receiver.handle) {
        Ok(_) => {}
        Err(e) => {
            let _ = sender.close();
            let _ = receiver.close();
            return Err(e);
        }
    };
    receiver.close()?;
    Ok(sender)
}

/// Creates a node and corresponding inbound channel of the same type, and returns [`Sender`] for
/// such channel.
#[cfg(feature = "linear-handles")] // linear handles version
pub fn node_create<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
    node_config: &crate::NodeConfiguration,
) -> Result<Sender<T>, OakStatus> {
    let (sender, receiver) = channel_create(&format!("{}-in", name), label)?;
    crate::node_create(name, node_config, label, receiver.into_inner())?;
    Ok(sender)
}

/// Uses the current node's label-downgrading privilege to create a node and corresponding inbound
/// channel of the same type, and returns a [`Sender`] for the channel.
#[cfg(not(feature = "linear-handles"))] // no linear handles version
pub fn node_create_with_downgrade<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
    node_config: &crate::NodeConfiguration,
) -> Result<Sender<T>, OakStatus> {
    let (sender, receiver) = channel_create_with_downgrade(&format!("{}-in", name), label)?;
    match crate::node_create_with_downgrade(name, node_config, label, receiver.handle) {
        Ok(_) => {}
        Err(e) => {
            let _ = sender.close();
            let _ = receiver.close();
            return Err(e);
        }
    };
    receiver.close()?;
    Ok(sender)
}

/// Uses the current node's label-downgrading privilege to create a node and corresponding inbound
/// channel of the same type, and returns a [`Sender`] for the channel.
#[cfg(feature = "linear-handles")] // linear handles version
pub fn node_create_with_downgrade<T: Encodable + Decodable>(
    name: &str,
    label: &Label,
    node_config: &crate::NodeConfiguration,
) -> Result<Sender<T>, OakStatus> {
    let (sender, receiver) = channel_create_with_downgrade(&format!("{}-in", name), label)?;
    crate::node_create_with_downgrade(name, node_config, label, receiver.into_inner())?;
    Ok(sender)
}

/// Creates a node and corresponding inbound channel of the same type, sends an init message to it,
/// and returns a [`Sender`] of command messages; for nodes that are instantiated via the
/// [`crate::entrypoint_command_handler_init`] macro.
pub fn entrypoint_node_create<
    T: crate::WasmEntrypoint<Message = oak_io::InitWrapper<Init, Command>>,
    Init: Encodable + Decodable,
    Command: Encodable + Decodable,
>(
    name: &str,
    label: &Label,
    wasm_module_name: &str,
    init: Init,
) -> Result<Sender<Command>, oak_io::OakError> {
    let node_config = &crate::node_config::wasm(wasm_module_name, T::ENTRYPOINT_NAME);
    let init_sender = node_create(name, label, node_config)?;
    let result = send_init(&init_sender, init, label);
    init_sender.close()?;
    result
}

/// Sends an init message over the provided [`Sender`], which is consumed by this method, and
/// returns a [`Sender`] for subsequent commands.
///
/// Useful for sending initial data to nodes instantiated via the
/// [`crate::entrypoint_command_handler_init`] macro.
fn send_init<Init, Command, InitSender>(
    sender: InitSender,
    init: Init,
    command_channel_label: &Label,
) -> Result<Sender<Command>, oak_io::OakError>
where
    Init: Encodable + Decodable,
    Command: Encodable + Decodable,
    // TODO(#1854): Only accept references once handles are always linear types
    InitSender: Borrow<Sender<oak_io::InitWrapper<Init, Command>>>,
{
    let (command_sender, command_receiver) =
        channel_create::<Command>("command sender", command_channel_label)?;
    let init_wrapper = oak_io::InitWrapper {
        init,
        command_receiver,
    };
    sender.borrow().send(&init_wrapper)?;
    Ok(command_sender)
}

/// Sends [`crate::grpc::Invocation`] (containing [`oak_io::Receiver`] and [`oak_io::Sender`])
/// through invocation sender if [`oak_io::Receiver`] label flows to invocation sender's label.
/// If failed - sends error back through [`oak_io::Sender`].
///
/// Useful for sending invocations from router nodes and checking label correctness without actually
/// reading the contents of invocation.
pub fn forward_invocation(
    invocation: crate::grpc::Invocation,
    invocation_sender: &Sender<crate::grpc::Invocation>,
) -> anyhow::Result<()> {
    match (&invocation.receiver, &invocation.sender) {
        (Some(request_receiver), Some(response_sender)) => {
            let request_label = request_receiver
                .label()
                .context("Couldn't read request label")?;
            let sender_label = invocation_sender
                .label()
                .context("Couldn't read invocation sender label")?;
            // Check if request label is valid in the context of invocation sender.
            if request_label.flows_to(&sender_label) {
                // Forward invocation through invocation sender.
                let result = invocation_sender
                    .send(&invocation)
                    .context("Couldn't forward invocation");
                // Close the channels.
                invocation.close()?;
                result
            } else {
                // Close the receiver channel separately.
                invocation
                    .receiver
                    .expect("Couldn't get receiver")
                    .close()
                    .expect("Couldn't close the receiver");
                // Return an error through `response_sender`.
                let grpc_response_writer =
                    crate::grpc::ChannelResponseWriter::new(response_sender.clone());
                grpc_response_writer
                    .close(Err(crate::grpc::build_status(
                        rpc::Code::InvalidArgument,
                        "Invalid request label",
                    )))
                    .context("Couldn't send error response back")?;
                Err(anyhow::anyhow!(
                    "Invalid request label: {:?}",
                    request_label
                ))
            }
        }
        _ => Err(anyhow::anyhow!("Received malformed invocation")),
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
