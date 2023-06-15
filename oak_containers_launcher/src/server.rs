//
// Copyright 2023 The Project Oak Authors
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

mod proto {
    pub mod oak {
        pub mod containers {
            tonic::include_proto!("oak.containers");
        }
    }
}

use self::proto::oak::containers::{
    launcher_server::{Launcher, LauncherServer},
    GetImageResponse,
};
use anyhow::anyhow;
use futures::Stream;
use std::pin::Pin;
use tokio_vsock::VsockListener;
use tonic::{transport::Server, Request, Response, Status};

type GetImageResponseStream = Pin<Box<dyn Stream<Item = Result<GetImageResponse, Status>> + Send>>;

#[derive(Default)]
struct LauncherServerImplementation {}

#[tonic::async_trait]
impl Launcher for LauncherServerImplementation {
    type GetOakSystemImageStream = GetImageResponseStream;
    type GetContainerBundleStream = GetImageResponseStream;

    async fn get_oak_system_image(
        &self,
        _request: Request<()>,
    ) -> Result<Response<Self::GetOakSystemImageStream>, tonic::Status> {
        let response_stream = async_stream::try_stream! {
          // TODO(#4023): Send a system image
          yield GetImageResponse::default();
        };

        Ok(Response::new(
            Box::pin(response_stream) as Self::GetOakSystemImageStream
        ))
    }

    async fn get_container_bundle(
        &self,
        _request: Request<()>,
    ) -> Result<Response<Self::GetContainerBundleStream>, tonic::Status> {
        let response_stream = async_stream::try_stream! {
          // TODO(#4023): Send an actual container
          yield GetImageResponse::default();
        };

        Ok(Response::new(
            Box::pin(response_stream) as Self::GetContainerBundleStream
        ))
    }
}

pub async fn new(vsock_cid: u32, vsock_port: u32) -> Result<(), anyhow::Error> {
    let server_impl = LauncherServerImplementation {};
    let vsock_listener = VsockListener::bind(vsock_cid, vsock_port)?.incoming();

    Server::builder()
        .add_service(LauncherServer::new(server_impl))
        .serve_with_incoming(vsock_listener)
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
