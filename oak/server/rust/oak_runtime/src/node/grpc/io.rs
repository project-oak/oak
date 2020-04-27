//
// Copyright 2020 The Project Oak Authors
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

use log::{debug, error};
use prost::Message;

use oak_abi::{
    proto::oak::encap::{GrpcRequest, GrpcResponse},
    ChannelReadStatus, Handle, OakStatus,
};

use crate::{runtime::RuntimeProxy, NodeMessage};

/// Wrapper for a [`Handle`] that is responsible for sending messages to an Oak channel.
/// Uses [`RuntimeProxy`] to send messages to a specific Oak Node.
pub struct Sender {
    runtime: RuntimeProxy,
    writer: Handle,
}

impl Sender {
    pub fn new(runtime: RuntimeProxy, writer: Handle) -> Self {
        Self { runtime, writer }
    }

    /// Composes a [`Message`] from `data` and `handles` and sends it to the [`Sender::writer`].
    pub fn send(&self, data: Vec<u8>, handles: Vec<Handle>) -> Result<(), OakStatus> {
        self.runtime
            .channel_write(self.writer, NodeMessage { data, handles })
    }
}

/// Wrapper for a [`Handle`] that is responsible for reading messages from an Oak channel.
/// Uses [`RuntimeProxy`] to read messages from a specific Oak Node.
pub struct Receiver {
    runtime: RuntimeProxy,
    reader: Handle,
}

impl Receiver {
    pub fn new(runtime: RuntimeProxy, reader: Handle) -> Self {
        Self { runtime, reader }
    }

    /// Waits and reads a [`Message`] from the [`Receiver::reader`].
    pub fn receive(&self) -> Result<NodeMessage, OakStatus> {
        let read_status = self.runtime.wait_on_channels(&[self.reader])?;

        if read_status[0] == ChannelReadStatus::ReadReady {
            self.runtime.channel_read(self.reader).and_then(|message| {
                message.ok_or_else(|| {
                    debug!("Channel read error {:?}: Empty message", self.reader);
                    OakStatus::ErrInternal
                })
            })
        } else {
            debug!("Channel read error {:?}: {:?}", self.reader, read_status[0]);
            Err(OakStatus::ErrInternal)
        }
    }
}

/// A gRPC invocation, consisting of exactly two channels: one to read incoming requests from the
/// client (wrapped in a [`Receiver`]), and one to write outgoing responses to the client (wrapped
/// in a [`Sender`]).
pub struct Invocation {
    receiver: Receiver,
    sender: Sender,
}

impl Invocation {
    /// Reads [`Message`] that contains two channel handles from [`Receiver`] and create
    /// [`Invocation`] from it.
    pub fn read(receiver: &Receiver) -> Result<Self, OakStatus> {
        let message = receiver.receive()?;

        if !message.data.is_empty() {
            error!(
                "Incorrect number of bytes received: {} (expected: 0)",
                message.data.len()
            );
            return Err(OakStatus::ErrInternal);
        }
        if message.handles.len() != 2 {
            error!(
                "Incorrect number of handles received: {} (expected: 2)",
                message.handles.len()
            );
            return Err(OakStatus::ErrInternal);
        }
        Ok(Self {
            receiver: Receiver::new(receiver.runtime.clone(), message.handles[0]),
            sender: Sender::new(receiver.runtime.clone(), message.handles[1]),
        })
    }

    /// Reads an [`GrpcRequest`] from the [`Invocation::receiver`].
    pub fn receive_request(&self) -> Result<GrpcRequest, OakStatus> {
        let message = self.receiver.receive()?;
        GrpcRequest::decode(message.data.as_ref()).map_err(|error| {
            error!("Couldn't decode Protobuf message: {}", error);
            OakStatus::ErrInternal
        })
    }

    /// Sends an [`GrpcResponse`] to the [`Invocation::sender`].
    pub fn send_response(&self, response: GrpcResponse) -> Result<(), OakStatus> {
        let mut bytes = Vec::new();
        response.encode(&mut bytes).map_err(|error| {
            error!("failed to serialize gRPC response: {}", error);
            OakStatus::ErrInternal
        })?;

        self.sender.send(bytes, vec![])
    }
}
