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
//

mod proto {
    pub mod oak {
        pub mod containers {
            tonic::include_proto!("oak.containers");
        }
    }
}

use anyhow::{Context, Result};
use proto::oak::containers::launcher_client::LauncherClient as GrpcLauncherClient;
use tokio_vsock::VsockStream;
use tonic::transport::{Channel, Endpoint, Uri};
use tower::service_fn;

static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

pub struct LauncherClient {
    inner: GrpcLauncherClient<Channel>,
}

impl LauncherClient {
    pub async fn new(launcher_vsock_cid: u32, launcher_vsock_port: u32) -> Result<Self> {
        let inner: GrpcLauncherClient<Channel> = {
            let channel = Endpoint::try_from(IGNORED_ENDPOINT_URI)
                .context("couldn't form endpoint")?
                .connect_with_connector(service_fn(move |_: Uri| {
                    VsockStream::connect(launcher_vsock_cid, launcher_vsock_port)
                }))
                .await
                .context("couldn't connect to VSOCK socket")?;

            GrpcLauncherClient::new(channel)
        };
        Ok(Self { inner })
    }

    pub async fn get_oak_system_image(&mut self) -> Result<Vec<u8>> {
        let mut stream = self
            .inner
            .get_oak_system_image(())
            .await
            .context("couldn't form streaming connection")?
            .into_inner();

        let mut image_buf: Vec<u8> = Vec::new();
        while let Some(mut load_response) = stream
            .message()
            .await
            .context("couldn't load message from stream")?
        {
            image_buf.append(&mut load_response.image_chunk);
        }

        Ok(image_buf)
    }
}
