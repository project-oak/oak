//
// Copyright 2025 The Project Oak Authors
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
//

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use anyhow::Context;
use oak_sdk_containers::{
    default_orchestrator_channel, InstanceEncryptionKeyHandle, OrchestratorClient,
};
use oak_sdk_server_v1::OakApplicationContext;
use println as debug;
use tokio::net::TcpListener;

const ENCLAVE_APP_PORT: u16 = 8080;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    debug!("Logging!");
    let orchestrator_channel =
        default_orchestrator_channel().await.context("failed to create orchestrator channel")?;

    let mut orchestrator_client = OrchestratorClient::create(&orchestrator_channel);

    let application_config = orchestrator_client
        .get_application_config()
        .await
        .context("failed to get application config")?;

    let endorsed_evidence = orchestrator_client
        .get_endorsed_evidence()
        .await
        .context("failed to get endorsed evidence")?;

    let encryption_key_handle = InstanceEncryptionKeyHandle::create(&orchestrator_channel);

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), ENCLAVE_APP_PORT);
    let listener = TcpListener::bind(addr).await?;

    let (_observer, metrics) = private_memory_server_lib::metrics::create_metrics();

    let join_handle = tokio::spawn(private_memory_server_lib::app_service::create(
        listener,
        OakApplicationContext::new(
            Box::new(encryption_key_handle),
            endorsed_evidence,
            Box::new(
                private_memory_server_lib::app::SealedMemoryHandler::new(
                    &application_config,
                    metrics.clone(),
                )
                .await,
            ),
        ),
        private_memory_server_lib::app::SealedMemoryHandler::new(
            &application_config,
            metrics.clone(),
        )
        .await,
        metrics,
    ));
    orchestrator_client.notify_app_ready().await.context("failed to notify that app is ready")?;
    debug!("Private memory is now serving!");
    join_handle.await??;
    debug!("Done!!");
    Ok(())
}
