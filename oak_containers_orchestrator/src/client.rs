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

use anyhow::Context;
use proto::oak::containers::launcher_client::LauncherClient as GrpcLauncherClient;
use tokio_vsock::VsockStream;
use tonic::transport::{Endpoint, Uri};
use tower::service_fn;

// Virtio VSOCK does not use URIs, hence this URI will never be used.
// It is defined purely since in order to create a channel, since a URI has to
// be supplied to create an `Endpoint`.
static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

/// Utility struct used to interface with the launcher
pub struct LauncherClient {
    inner: GrpcLauncherClient<tonic::transport::channel::Channel>,
}

impl LauncherClient {
    pub async fn create(address: vsock::VsockAddr) -> Result<Self, Box<dyn std::error::Error>> {
        let inner: GrpcLauncherClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::try_from(IGNORED_ENDPOINT_URI)
                .context("couldn't form endpoint")?
                .connect_with_connector(service_fn(move |_: Uri| {
                    VsockStream::connect(address.cid(), address.port())
                }))
                .await
                .context("couldn't connect to VSOCK socket")?;

            GrpcLauncherClient::new(channel)
        };
        Ok(Self { inner })
    }

    pub async fn get_container_bundle(&mut self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let mut stream = self
            .inner
            .get_container_bundle(())
            .await
            .context("couldn't form streaming connection")?
            .into_inner();

        let mut container_buf: Vec<u8> = Vec::new();
        while let Some(mut load_response) = stream
            .message()
            .await
            .context("couldn't load message from stream")?
        {
            container_buf.append(&mut load_response.image_chunk);
        }

        Ok(container_buf)
    }
}
