//
// Copyright 2021 The Project Oak Authors
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

//! Functionality for distributed runtime.

use oak_abi::OakStatus;

use crate::{Downgrading, NodeId, NodeMessage};

pub mod client;
pub mod server;

/// Remote Runtime functionality.
pub trait RemoteRuntime {
    /// Similar to `channel_read` in the Runtime, but for channels on a remote Runtime. Reads a
    /// message from a channel. Fails with [`OakStatus::ErrChannelClosed`] if the underlying
    /// channel is empty and has been orphaned.
    fn remote_channel_read(
        &self,
        node_id: NodeId,
        read_handle: oak_abi::Handle,
        downgrade: Downgrading,
    ) -> Result<Option<NodeMessage>, OakStatus>;

    /// Similar to `channel_write` in the Runtime, but for channels on a remote Runtime. Writes a
    /// message to a channel. Fails with [`OakStatus::ErrChannelClosed`] if the underlying
    /// channel has been orphaned.
    fn remote_channel_write(
        &self,
        node_id: NodeId,
        write_handle: oak_abi::Handle,
        node_msg: NodeMessage,
        downgrade: Downgrading,
    ) -> Result<(), OakStatus>;
}
