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

use anyhow::{anyhow, Context};
use clap::Parser;
use oak_containers_orchestrator_client::LauncherClient;
use oak_functions_containers_app::{orchestrator_client::OrchestratorClient, serve};
use opentelemetry_api::global::set_error_handler;
use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use tokio::net::TcpListener;

const OAK_FUNCTIONS_CONTAINERS_APP_PORT: u16 = 8080;

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let launcher_client = Arc::new(
        LauncherClient::create(args.launcher_addr.parse()?)
            .await
            .map_err(|error| anyhow!("couldn't create client: {:?}", error))?,
    );

    // Use eprintln here, as normal logging would go through the OTLP connection, which may no
    // longer be valid.
    set_error_handler(|err| eprintln!("oak_functions_containers_app: OTLP error: {}", err))?;

    let metrics = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .with_exporter(launcher_client.openmetrics_builder())
        .with_period(Duration::from_secs(60))
        .build()?;

    let mut client = OrchestratorClient::create()
        .await
        .context("couldn't create Orchestrator client")?;

    // To be used when connecting trusted app to orchestrator.
    let _application_config = client.get_application_config().await?;

    let addr = SocketAddr::new(
        IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        OAK_FUNCTIONS_CONTAINERS_APP_PORT,
    );
    let listener = TcpListener::bind(addr).await?;
    let server_handle = tokio::spawn(serve(listener, Arc::new(client.clone()), metrics));

    eprintln!("Running Oak Functions on Oak Containers at address: {addr}");
    client.notify_app_ready().await?;
    Ok(server_handle.await??)
}
