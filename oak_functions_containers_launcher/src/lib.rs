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
    }
}

mod oak_functions_client;

use crate::proto::oak::functions::{InitializeRequest, InitializeResponse};
use oak_containers_launcher::Launcher;

pub struct UntrustedApp {
    launcher: Launcher,
    oak_functions_client: oak_functions_client::OakFunctionsClient,
}

impl UntrustedApp {
    pub async fn create(
        launcher_args: oak_containers_launcher::Args,
    ) -> Result<Self, anyhow::Error> {
        let mut launcher = oak_containers_launcher::Launcher::create(launcher_args).await?;
        let trusted_app_address = launcher.get_trusted_app_address().await?;

        let oak_functions_client = oak_functions_client::OakFunctionsClient::create(format!(
            "http://{trusted_app_address}"
        ))
        .await?;
        Ok(Self {
            launcher,
            oak_functions_client,
        })
    }

    pub async fn initialize_enclave(
        &mut self,
        initialize_request: InitializeRequest,
    ) -> Result<InitializeResponse, Box<dyn std::error::Error>> {
        self.oak_functions_client
            .initialize(initialize_request)
            .await
    }

    pub async fn kill(&mut self) {
        self.launcher.kill().await;
    }
}
