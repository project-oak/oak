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
    RuntimeProxy,
};
use oak_io::Message;
use std::sync::Mutex;
use tonic::{Request, Response, Status};

pub struct RemoteRuntimeHandler {
    runtime: RuntimeProxy,
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
        Ok(Response::new(AddRemoteResponse {}))
    }

    async fn node_create(
        &self,
        _req: Request<NodeCreateRequest>,
    ) -> Result<Response<NodeCreateResponse>, Status> {
        // TODO
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
            handles: request.handles,
        };
        self.runtime
            .channel_write(request.write_handle, msg)
            .map_err(|err| Status::internal(format!("{}", err)))?;
        Ok(Response::new(ChannelWriteResponse {}))
    }
}
// This start a server to listen on a port
