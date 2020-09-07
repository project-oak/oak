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

use crate::RuntimeProxy;
use log::{error, info};
use oak_abi::{ChannelReadStatus, OakStatus};
use oak_io::{Decodable, Encodable, OakError};
pub use oak_io::{Receiver, Sender};

/// Extension trait for runtime-specific Receiver functionality.
pub trait ReceiverExt<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakError>;

    /// Waits, reads and decodes a message from the [`Receiver::handle`].
    fn receive(&self, runtime: &RuntimeProxy) -> Result<T, OakError>;
}

impl<T: Decodable> ReceiverExt<T> for Receiver<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakError> {
        runtime
            .channel_close(self.handle.handle)
            .map_err(|error| error.into())
    }

    /// Waits, reads and decodes a message from the [`Receiver::handle`].
    fn receive(&self, runtime: &RuntimeProxy) -> Result<T, OakError> {
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
                .map_err(|error| error.into())
                .and_then(|message| T::decode(&message)),
            ChannelReadStatus::Orphaned => {
                info!("Channel closed {:?}", self.handle);
                Err(OakStatus::ErrChannelClosed.into())
            }
            status => {
                error!("Channel read error {:?}: {:?}", self.handle, status);
                Err(OakStatus::ErrInternal.into())
            }
        }
    }
}

/// Extension trait for runtime-specific Sender functionality.
pub trait SenderExt<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakError>;

    /// Encodes and sends a message to the [`Sender::handle`].
    fn send(&self, message: T, runtime: &RuntimeProxy) -> Result<(), OakError>;
}

impl<T: Encodable> SenderExt<T> for Sender<T> {
    /// Close the underlying channel handle.
    fn close(self, runtime: &RuntimeProxy) -> Result<(), OakError> {
        runtime
            .channel_close(self.handle.handle)
            .map_err(|error| error.into())
    }

    /// Encodes and sends a message to the [`Sender::handle`].
    fn send(&self, message: T, runtime: &RuntimeProxy) -> Result<(), OakError> {
        runtime
            .channel_write(self.handle.handle, message.encode()?)
            .map_err(|error| error.into())
    }
}
