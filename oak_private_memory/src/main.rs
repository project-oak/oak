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
use oak_sdk_containers::{OrchestratorClient, default_orchestrator_channel};
use private_memory_server_lib::log::debug;
use tokio::net::TcpListener;

const ENCLAVE_APP_PORT: u16 = 8080;

use private_memory_server_lib::app::run_persistence_service;
use tokio::sync::mpsc;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    private_memory_server_lib::log::init_logging(true);
    debug!("Logging!");
    let orchestrator_channel =
        default_orchestrator_channel().await.context("failed to create orchestrator channel")?;

    let mut orchestrator_client = OrchestratorClient::create(&orchestrator_channel);

    let application_config_bytes = orchestrator_client
        .get_application_config()
        .await
        .context("failed to get application config")?;

    let application_config: private_memory_server_lib::app::ApplicationConfig =
        serde_json::from_slice(application_config_bytes.as_slice())
            .expect("Invalid application config");

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), ENCLAVE_APP_PORT);
    let listener = TcpListener::bind(addr).await?;

    let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
    let persistence_join_handle = tokio::spawn(run_persistence_service(persistence_rx));

    let metrics = private_memory_server_lib::metrics::get_global_metrics();
    let join_handle = tokio::spawn(private_memory_server_lib::app::service::create(
        listener,
        application_config,
        metrics,
        persistence_tx,
        std::sync::Arc::new(attestation::default_server_session_config),
    ));
    orchestrator_client.notify_app_ready().await.context("failed to notify that app is ready")?;
    debug!("Private memory is now serving!");
    join_handle.await??;

    persistence_join_handle.await?;

    debug!("Done!!");
    Ok(())
}
