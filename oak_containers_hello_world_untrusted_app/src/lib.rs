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

use oak_containers_launcher::Launcher;

mod app_client;

/// The local address that will be forwarded by the VMM to the guest on port 8080.
const UNTRUSTED_APP_ADDRESS: &str = "http://127.0.0.1:8088";

pub struct UntrustedApp {
    launcher: Launcher,
    app_client: app_client::TrustedApplicationClient,
}

impl UntrustedApp {
    pub async fn create(
        launcher_args: oak_containers_launcher::Args,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let launcher = oak_containers_launcher::Launcher::create(launcher_args).await?;
        // TODO(#4194): Stop sleeping once we have a mechanism to notify the untrusted app that the
        // tursted app is ready.
        tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
        let app_client =
            app_client::TrustedApplicationClient::create(UNTRUSTED_APP_ADDRESS).await?;
        Ok(Self {
            launcher,
            app_client,
        })
    }

    pub async fn hello(&mut self, name: &str) -> Result<String, Box<dyn std::error::Error>> {
        self.app_client.hello(name).await
    }

    pub async fn kill(&mut self) {
        self.launcher.kill().await;
    }
}
