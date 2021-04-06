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

//! Functionality for serving remote runtimes.

use super::client::RemoteClients;
use crate::{
    proto::oak::remote::{
        encap::{
            AddRemoteRequest, AddRemoteResponse, ChannelWriteRequest, ChannelWriteResponse,
            NodeCreateRequest, NodeCreateResponse,
        },
        remote_runtime_server::RemoteRuntime,
    },
    RuntimeProxy,
};
use maplit::hashmap;
use oak_io::Message;
use std::sync::Mutex;
use tonic::{Request, Response, Status};

pub struct RemoteRuntimeHandler {
    runtime: RuntimeProxy,
    runtime_uuid: String,
    // List of clients for remote Runtime instances that are connected to this Runtime.
    remotes: Mutex<RemoteClients>,
}

// TODO: Consider implementing RemoteRuntime for the Runtime or RuntimeProxy.
#[tonic::async_trait]
impl RemoteRuntime for RemoteRuntimeHandler {
    async fn add_remote(
        &self,
        req: Request<AddRemoteRequest>,
    ) -> Result<Response<AddRemoteResponse>, Status> {
        log::info!("Processing the add_remote request");
        self.remotes
            .lock()
            .unwrap()
            .add_remote(req.into_inner().remote_address);
        Ok(Response::new(AddRemoteResponse {
            runtime_uuid: self.runtime_uuid.clone(),
        }))
    }

    async fn node_create(
        &self,
        _req: Request<NodeCreateRequest>,
    ) -> Result<Response<NodeCreateResponse>, Status> {
        // TODO
        // Create a channel with read/write handles. The read handle should be used as the
        // startup_handle to the node. The write handle should be registered here as the send/write
        // end for the init_handle in the request. This mapping is then used in
        // `remote_channel_write` to write the message to the correct channel.
        // For each of the senders and receivers in the initial message create channels and
        // DummySender nodes as needed.
        log::info!("Processing the node_create request");
        Ok(Response::new(NodeCreateResponse {
            remote_node_id: 0,
            handles_map: hashmap! {},
        }))
    }

    async fn channel_write(
        &self,
        req: Request<ChannelWriteRequest>,
    ) -> Result<Response<ChannelWriteResponse>, Status> {
        log::info!("Processing the channel_write request");
        let request = req.into_inner();
        let msg = Message {
            bytes: request.data,
            // TODO: For each handle create a channel. For sender handles, in addition create a
            // DummySender node with the receiver handle in it. The receiver handles should have a
            // DummySender on the other side. Create a mapping between (remote) receiver handles,
            // and local sender ends. Return the mapping in the response to the remote.
            handles: request
                .handles
                .into_iter()
                .map(|handle| handle.raw_handle)
                .collect(),
        };

        // The `request.write_handle.raw_handle` should refer to a valid write handle on this
        // Runtime.
        //
        // TODO: what about its label, and the label of the node that is writing into it?
        let handle = request.write_handle;
        self.runtime
            .channel_write(handle, msg)
            .map_err(|err| Status::internal(format!("{}", err)))?;
        Ok(Response::new(ChannelWriteResponse {
            handles_map: hashmap! {},
        }))
    }
}
