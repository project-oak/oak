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

use anyhow::{Context, Result};
use oak_containers_channel::create_channel;
use oak_grpc::oak::containers::launcher_client::LauncherClient as GrpcLauncherClient;
use tonic::transport::{Channel, Uri};

pub struct LauncherClient {
    inner: GrpcLauncherClient<Channel>,
}

impl LauncherClient {
    pub async fn new(addr: Uri) -> Result<Self> {
        let inner = GrpcLauncherClient::new(create_channel(addr).await?);
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
        while let Some(mut load_response) =
            stream.message().await.context("couldn't load message from stream")?
        {
            image_buf.append(&mut load_response.image_chunk);
        }

        Ok(image_buf)
    }
}
