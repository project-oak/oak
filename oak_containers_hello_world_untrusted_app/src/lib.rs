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

mod app_client;

use oak_containers_launcher::Launcher;
use std::net::Ipv4Addr;

/// The local address that will be forwarded by the VMM to the guest's IP adress.
const PROXY_ADDRESS: Ipv4Addr = Ipv4Addr::LOCALHOST;

pub struct UntrustedApp {
    launcher: Launcher,
    app_client: app_client::TrustedApplicationClient,
}

impl UntrustedApp {
    pub async fn create(
        launcher_args: oak_containers_launcher::Args,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let mut launcher = oak_containers_launcher::Launcher::create(launcher_args).await?;
        let proxy_port = launcher.get_proxy_port();
        log::info!("Assigned port {proxy_port} for proxying requests to the trusted app");
        // We ignore the address provided by the trusted application, since the VMM will proxy the
        // connection from the host's local address and port to the VM guest's listening
        // address and port.
        let _trusted_app_address = launcher.get_trusted_app_address().await?;
        let app_client = app_client::TrustedApplicationClient::create(format!(
            "http://{PROXY_ADDRESS}:{proxy_port}"
        ))
        .await?;
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
