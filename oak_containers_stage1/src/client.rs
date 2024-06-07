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
        pub use oak_attestation::proto::oak::attestation;
    }
}

use anyhow::{Context, Result};
use proto::oak::containers::launcher_client::LauncherClient as GrpcLauncherClient;
use tokio_vsock::{VsockAddr, VsockStream};
use tonic::transport::{Channel, Uri};
use tower::service_fn;

pub struct LauncherClient {
    inner: GrpcLauncherClient<Channel>,
}

impl LauncherClient {
    pub async fn new(addr: Uri) -> Result<Self> {
        // vsock is unfortunately going to require special handling.
        let inner = if addr.scheme_str() == Some("vsock") {
            let vsock_addr = VsockAddr::new(
                addr.host()
                    .unwrap_or(format!("{}", tokio_vsock::VMADDR_CID_HOST).as_str())
                    .parse()
                    .context("invalid vsock CID")?,
                addr.port_u16().context("invalid vsock port")?.into(),
            );
            // The C++ gRPC implementations are more particular about the URI scheme; in
            // particular, they may get confused by the "vsock" scheme. Therfore, create a
            // fake URI with the "http" scheme to placate the libraries; the actual
            // connection is made in `connect_with_connector` and that uses the correct URI.
            GrpcLauncherClient::new(
                Channel::builder(Uri::from_static("http://0:0"))
                    .connect_with_connector(service_fn(move |_| VsockStream::connect(vsock_addr)))
                    .await?,
            )
        } else {
            GrpcLauncherClient::<Channel>::connect(addr).await?
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
        while let Some(mut load_response) =
            stream.message().await.context("couldn't load message from stream")?
        {
            image_buf.append(&mut load_response.image_chunk);
        }

        Ok(image_buf)
    }
}
