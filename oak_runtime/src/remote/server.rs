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
        remote_runtime_server::RemoteRuntime, AddRemoteRequest, AddRemoteResponse,
        ChannelReadRequest, ChannelReadResponse, ChannelWriteRequest, ChannelWriteResponse,
        NodeCreateRequest, NodeCreateResponse,
    },
    Downgrading, NodeId, Runtime,
};
use oak_io::Message;
use std::sync::Mutex;
use tonic::{Request, Response, Status};

pub struct RemoteRuntimeHandler {
    runtime: Runtime,
    runtime_uuid: String,
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
        // register remote channel with the node.
        // on success remote runtime should increase reader counts on the channel.
        log::info!("Processing the node_create request");
        Ok(Response::new(NodeCreateResponse { remote_node_id: 0 }))
    }

    async fn channel_read(
        &self,
        _req: Request<ChannelReadRequest>,
    ) -> Result<Response<ChannelReadResponse>, Status> {
        // TODO
        log::info!("Processing the channel_read request");
        Ok(Response::new(ChannelReadResponse {
            data: vec![],
            handles: vec![],
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
            // TODO: replace handles in Message with the one in the remote.proto, with remote
            // runtime ID.
            handles: request
                .handles
                .into_iter()
                .map(|handle| handle.raw_handle)
                .collect(),
        };
        let downgrading = if request.downgrade {
            Downgrading::Yes
        } else {
            Downgrading::No
        };
        // TODO: fetch the actual channel half corresponding to `request.write_handle` from the
        // runtime
        let handle = 0;
        self.runtime
            .channel_write(NodeId(request.node_id), handle, msg, downgrading)
            .map_err(|err| Status::internal(format!("{}", err)))?;
        Ok(Response::new(ChannelWriteResponse {}))
    }
}
