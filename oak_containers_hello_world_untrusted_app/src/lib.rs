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

const UNTRUSTED_APP_VSOCK_CID: u32 = vsock::VMADDR_CID_HOST;
const UNTRUSTED_APP_VSOCK_PORT: u32 = 8081;

pub struct UntrustedApp {
    launcher_handle: tokio::task::JoinHandle<Result<(), anyhow::Error>>,
    app_client: app_client::TrustedApplicationClient,
}

impl UntrustedApp {
    pub async fn create(
        launcher_args: oak_containers_launcher::Args,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let launcher_handle = tokio::task::spawn(oak_containers_launcher::create(launcher_args));
        let app_client = app_client::TrustedApplicationClient::create(
            UNTRUSTED_APP_VSOCK_CID,
            UNTRUSTED_APP_VSOCK_PORT,
        )
        .await?;

        Ok(Self {
            launcher_handle,
            app_client,
        })
    }

    pub async fn hello(&mut self, name: &str) -> Result<String, Box<dyn std::error::Error>> {
        self.app_client.hello(name).await
    }
}

impl std::ops::Drop for UntrustedApp {
    fn drop(&mut self) {
        // Shutdown the running launcher & VM.
        self.launcher_handle.abort();
    }
}
