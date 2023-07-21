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
    trusted_application_server::{TrustedApplication, TrustedApplicationServer},
    HelloRequest, HelloResponse,
};
use anyhow::anyhow;
use std::net::SocketAddr;

#[derive(Default)]
struct TrustedApplicationImplementation {
    application_config: Vec<u8>,
}

#[tonic::async_trait]
impl TrustedApplication for TrustedApplicationImplementation {
    async fn hello(
        &self,
        request: tonic::Request<HelloRequest>,
    ) -> Result<tonic::Response<HelloResponse>, tonic::Status> {
        let name = request.into_inner().name;
        let greeting: String = format!("Hello from the trusted side, {}! Btw, the Trusted App has a config with a length of {} bytes.", name, self.application_config.len());
        let response = tonic::Response::new(HelloResponse { greeting });
        Ok(response)
    }
}

pub async fn create(addr: SocketAddr, application_config: Vec<u8>) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(TrustedApplicationServer::new(
            TrustedApplicationImplementation { application_config },
        ))
        .serve(addr)
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
