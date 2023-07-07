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

// This is a Frankenstein between the Oak Containers Hello World client and a HTTP client for experimenting.

mod proto {
    pub mod oak {
        pub mod containers {
          pub mod example {
            tonic::include_proto!("oak.containers.example");
        }
      }
    }
}

use proto::oak::containers::example::{EchoRequest, example_client::ExampleClient as GrpcUntrustedApplicationClient};
use tokio_vsock::VsockStream;
use tonic::transport::{Endpoint, Uri};
use anyhow::Context;
use tower::service_fn;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {

// Change to use http or vsock.
let use_vsock = true;

if use_vsock {
    let mut untrusted_app_client =
    UntrustedApplicationClient::create(1, 8080).await?;
    let _greeting = untrusted_app_client.echo().await?;
} else {
    let mut client = GrpcUntrustedApplicationClient::connect("http://[::1]:8080").await?;
    let request = tonic::Request::new(EchoRequest {
      message : "Hello World".to_string()
    });
    let response = client.echo(request).await?;
    println!("Got: '{}' from service", response.into_inner().message);
}
Ok(())
}

// Virtio VSOCK does not use URIs, hence this URI will never be used.
// It is defined purely since in order to create a channel, since a URI has to
// be supplied to create an `Endpoint`.
static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

/// Utility struct used to interface with the launcher
pub struct UntrustedApplicationClient {
    inner: GrpcUntrustedApplicationClient<tonic::transport::channel::Channel>,
}

impl UntrustedApplicationClient {
    pub async fn create(
        untrusted_application_vsock_cid: u32,
        untrusted_application_vsock_port: u32,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let inner: GrpcUntrustedApplicationClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::try_from(IGNORED_ENDPOINT_URI)
                .context("couldn't form endpoint")?
                .connect_with_connector(service_fn(move |_: Uri| {
                    VsockStream::connect(
                        untrusted_application_vsock_cid,
                        untrusted_application_vsock_port,
                    )
                }))
                .await
                .context("couldn't connect to VSOCK socket")?;

            GrpcUntrustedApplicationClient::new(channel)
        };
        Ok(Self { inner })
    }

    pub async fn echo(&mut self) -> Result<String, Box<dyn std::error::Error>> {
        let greeting = self
            .inner
            .echo(EchoRequest {
                message: "Hello World".to_string(),
            })
            .await?
            .into_inner()
            .message;
        Ok(greeting)
    }
}