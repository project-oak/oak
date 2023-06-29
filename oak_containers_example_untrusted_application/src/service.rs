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
            pub mod example {
                tonic::include_proto!("oak.containers.example");
            }
        }
    }
}

use self::proto::oak::containers::example::{
    untrusted_application_server::{UntrustedApplication, UntrustedApplicationServer},
    HelloRequest, HelloResponse,
};
use anyhow::anyhow;
use tokio_vsock::VsockListener;

#[derive(Default)]
struct UntrustedApplicationImplementation {}

#[tonic::async_trait]
impl UntrustedApplication for UntrustedApplicationImplementation {
    async fn hello(
        &self,
        request: tonic::Request<HelloRequest>,
    ) -> Result<tonic::Response<HelloResponse>, tonic::Status> {
        println!(
            "Received a HelloRequest from the trusted application: {:?}",
            request
        );
        let name = request.into_inner().name;
        let greeting: String = format!("Hello from the untrusted launcher, {}!", name);
        let response = tonic::Response::new(HelloResponse { greeting });
        println!(
            "Responded to the HelloRequest with the following HelloResponse: {:?}",
            response
        );
        Ok(response)
    }
}

pub async fn create(
    untrusted_application_vsock_cid: u32,
    untrusted_application_vsock_port: u32,
) -> Result<(), anyhow::Error> {
    let server_impl = UntrustedApplicationImplementation {};
    let vsock_listener = VsockListener::bind(
        untrusted_application_vsock_cid,
        untrusted_application_vsock_port,
    )?
    .incoming();

    tonic::transport::Server::builder()
        .add_service(UntrustedApplicationServer::new(server_impl))
        .serve_with_incoming(vsock_listener)
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
