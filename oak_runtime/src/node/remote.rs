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

//! Functionality for communication with a remote Runtime.

use crate::{
    node::{ConfigurationError, Node},
    remote::RemoteRuntime,
    RuntimeProxy,
};
use tokio::sync::oneshot;

/// ExternalConnection node that can serve as a stub for a remote Runtime.
pub struct ExternalConnectionNode {
    /// Pseudo-Node name.
    node_name: String,
}

impl ExternalConnectionNode {
    pub fn new(node_name: &str) -> Result<Self, ConfigurationError> {
        Ok(ExternalConnectionNode {
            node_name: node_name.to_string(),
        })
    }
}

impl Node for ExternalConnectionNode {
    fn node_type(&self) -> &'static str {
        "external-connection"
    }

    fn run(
        self: Box<Self>,
        _runtime: RuntimeProxy,
        _startup_handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        // TODO
    }
}

impl RemoteRuntime for ExternalConnectionNode {
    fn remote_channel_read(
        &self,
        node_id: NodeId,
        read_handle: oak_abi::Handle,
        downgrade: Downgrading,
    ) -> Result<Option<NodeMessage>, OakStatus> {
        // TODO: implement
        OK(None)
    }

    fn remote_channel_write(
        &self,
        node_id: NodeId,
        write_handle: oak_abi::Handle,
        node_msg: NodeMessage,
        downgrade: Downgrading,
    ) -> Result<(), OakStatus> {
        // TODO: implement
        OK(())
    }
}
