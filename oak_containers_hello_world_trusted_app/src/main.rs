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

use anyhow::anyhow;
use oak_containers_hello_world_trusted_app::orchestrator_client::OrchestratorClient;
use oak_containers_sdk::EncryptionKeyHandle;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use tokio::net::TcpListener;

const TRUSTED_APP_PORT: u16 = 8080;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = OrchestratorClient::create()
        .await
        .map_err(|error| anyhow!("couldn't create Orchestrator client: {:?}", error))?;
    let application_config = client.clone().get_application_config().await?;
    let encryption_key_handle = EncryptionKeyHandle::create()
        .await
        .map_err(|error| anyhow!("couldn't create encryption key handle: {:?}", error))?;
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), TRUSTED_APP_PORT);
    let listener = TcpListener::bind(addr).await?;
    let join_handle = tokio::spawn(oak_containers_hello_world_trusted_app::app_service::create(
        listener,
        application_config,
        encryption_key_handle,
    ));
    client.notify_app_ready().await?;
    join_handle.await??;
    Ok(())
}
