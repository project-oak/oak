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

//! Helper types for data structures that can be transmitted over channels.

use crate::{NodeMessage, RuntimeProxy};
use log::{error, info};
use oak_abi::{ChannelReadStatus, OakStatus};
use oak_io::handle::{ReadHandle, WriteHandle};

/// A trait for objects that can be decoded from bytes + handles.
pub trait Decodable: Sized {
    fn decode(message: &NodeMessage) -> Result<Self, OakStatus>;
}

impl<T: prost::Message + std::default::Default> Decodable for T {
    fn decode(message: &NodeMessage) -> Result<Self, OakStatus> {
        if !message.handles.is_empty() {
            error!("Non-empty handles field");
            return Err(OakStatus::ErrInternal);
        }
        let value = T::decode(message.data.as_slice()).map_err(|error| {
            error!("Couldn't decode Protobuf message: {}", error);
            OakStatus::ErrInternal
        })?;
        Ok(value)
    }
}

/// A trait for objects that can be encoded as bytes + handles.
pub trait Encodable {
    fn encode(&self) -> Result<NodeMessage, OakStatus>;
}

impl<T: prost::Message> Encodable for T {
    fn encode(&self) -> Result<NodeMessage, OakStatus> {
        let mut data = Vec::new();
        self.encode(&mut data).map_err(|error| {
            error!("Couldn't encode Protobuf message: {}", error);
            OakStatus::ErrInternal
        })?;
        let handles = Vec::new();
        Ok(NodeMessage { data, handles })
    }
}

/// Wrapper for a [`Handle`] that is responsible for reading messages from an Oak channel.
pub struct Receiver<T: Decodable> {
    handle: ReadHandle,
    phantom: std::marker::PhantomData<T>,
}

impl<T: Decodable> Receiver<T> {
    pub fn new(handle: ReadHandle) -> Self {
        Self {
            handle,
            phantom: std::marker::PhantomData,
        }
    }
}

/// Extension trait for runtime-specific Receiver functionality.
pub trait ReceiverExt<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakStatus>;

    /// Waits, reads and decodes a message from the [`Receiver::handle`].
    fn receive(&self, runtime: &RuntimeProxy) -> Result<T, OakStatus>;
}

impl<T: Decodable> ReceiverExt<T> for Receiver<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakStatus> {
        runtime.channel_close(self.handle.handle)
    }

    /// Waits, reads and decodes a message from the [`Receiver::handle`].
    fn receive(&self, runtime: &RuntimeProxy) -> Result<T, OakStatus> {
        let read_status = runtime.wait_on_channels(&[self.handle.handle])?;

        match read_status[0] {
            ChannelReadStatus::ReadReady => runtime
                .channel_read(self.handle.handle)
                .and_then(|message| {
                    message.ok_or_else(|| {
                        error!("Channel read error {:?}: Empty message", self.handle);
                        OakStatus::ErrInternal
                    })
                })
                .and_then(|message| T::decode(&message)),
            ChannelReadStatus::Orphaned => {
                info!("Channel closed {:?}", self.handle);
                Err(OakStatus::ErrChannelClosed)
            }
            status => {
                error!("Channel read error {:?}: {:?}", self.handle, status);
                Err(OakStatus::ErrInternal)
            }
        }
    }
}

/// Wrapper for a [`Handle`] that is responsible for sending messages to an Oak channel.
pub struct Sender<T: Encodable> {
    handle: WriteHandle,
    phantom: std::marker::PhantomData<T>,
}

impl<T: Encodable> Sender<T> {
    pub fn new(handle: WriteHandle) -> Self {
        Self {
            handle,
            phantom: std::marker::PhantomData,
        }
    }
}

/// Extension trait for runtime-specific Sender functionality.
pub trait SenderExt<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakStatus>;

    /// Encodes and sends a message to the [`Sender::handle`].
    fn send(&self, message: T, runtime: &RuntimeProxy) -> Result<(), OakStatus>;
}

impl<T: Encodable> SenderExt<T> for Sender<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakStatus> {
        runtime.channel_close(self.handle.handle)
    }

    /// Encodes and sends a message to the [`Sender::handle`].
    fn send(&self, message: T, runtime: &RuntimeProxy) -> Result<(), OakStatus> {
        runtime.channel_write(self.handle.handle, message.encode()?)
    }
}
