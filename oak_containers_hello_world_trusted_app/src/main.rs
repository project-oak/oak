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

use anyhow::Context;
use oak_containers_sdk::{InstanceEncryptionKeyHandle, OrchestratorClient};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use tokio::net::TcpListener;

const TRUSTED_APP_PORT: u16 = 8080;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = OrchestratorClient::create()
        .await
        .context("Could't create orchestrator client")?;

    let application_config = client
        .get_application_config()
        .await
        .context("failed to get application config")?;

    let encryption_key_handle = InstanceEncryptionKeyHandle::create()
        .await
        .context("couldn't create encryption key handle: {:?}")?;
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), TRUSTED_APP_PORT);
    let listener = TcpListener::bind(addr).await?;
    let join_handle = tokio::spawn(oak_containers_hello_world_trusted_app::app_service::create(
        listener,
        application_config,
        encryption_key_handle,
    ));
    client
        .notify_app_ready()
        .await
        .context("failed to notify that app is ready")?;
    join_handle.await??;
    Ok(())
}
