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

use crate::proto::oak::functions::{
    oak_functions_client::OakFunctionsClient as GrpcOakFunctionsClient, InitializeRequest,
    InitializeResponse,
};
use anyhow::Context;
use tokio::time::Duration;
use tonic::transport::Endpoint;

/// Utility struct used to interface with the launcher
pub struct OakFunctionsClient {
    inner: GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
}

impl OakFunctionsClient {
    pub async fn create(server_addr: String) -> Result<Self, Box<dyn std::error::Error>> {
        let inner: GrpcOakFunctionsClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::from_shared(server_addr)
                .context("couldn't form channel")?
                .connect_timeout(Duration::from_secs(120))
                .connect()
                .await
                .context("couldn't connect to trusted app")?;
            GrpcOakFunctionsClient::new(channel)
        };
        Ok(Self { inner })
    }

    pub async fn initialize(
        &mut self,
        initialize_request: InitializeRequest,
    ) -> Result<InitializeResponse, Box<dyn std::error::Error>> {
        let initialize_response = self
            .inner
            .initialize(initialize_request)
            .await
            .context("couldn't send initialize request")?
            .into_inner();
        Ok(initialize_response)
    }
}
