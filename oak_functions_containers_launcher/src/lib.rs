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

pub mod proto {
    pub mod oak {
        pub mod functions {
            tonic::include_proto!("oak.functions");
        }
        pub use oak_crypto::proto::oak::crypto;
    }
}

use crate::proto::oak::functions::{
    oak_functions_client::OakFunctionsClient as GrpcOakFunctionsClient, InitializeRequest,
    InitializeResponse,
};
use anyhow::Context;
use oak_containers_launcher::Launcher;
use tokio::time::Duration;
use tonic::transport::Endpoint;

pub struct UntrustedApp {
    launcher: Launcher,
    oak_functions_client: GrpcOakFunctionsClient<tonic::transport::channel::Channel>,
}

impl UntrustedApp {
    pub async fn create(launcher_args: oak_containers_launcher::Args) -> anyhow::Result<Self> {
        let mut launcher = oak_containers_launcher::Launcher::create(launcher_args).await?;
        let trusted_app_address = launcher.get_trusted_app_address().await?;

        let oak_functions_client: GrpcOakFunctionsClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::from_shared(format!("http://{trusted_app_address}"))
                .context("couldn't form channel")?
                .connect_timeout(Duration::from_secs(120))
                .connect()
                .await
                .context("couldn't connect to trusted app")?;
            GrpcOakFunctionsClient::new(channel)
        };

        Ok(Self {
            launcher,
            oak_functions_client,
        })
    }

    pub async fn initialize_enclave(
        &mut self,
        initialize_request: InitializeRequest,
    ) -> Result<InitializeResponse, Box<dyn std::error::Error>> {
        let initialize_response = self
            .oak_functions_client
            .initialize(initialize_request)
            .await
            .context("couldn't send initialize request")?
            .into_inner();
        Ok(initialize_response)
    }

    pub async fn kill(&mut self) {
        self.launcher.kill().await;
    }
}
