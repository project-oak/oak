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
use oak_containers_orchestrator::launcher_client::LauncherClient;
use oak_containers_sdk::InstanceEncryptionKeyHandle;
use oak_functions_containers_app::{orchestrator_client::OrchestratorClient, serve};
use opentelemetry_api::{global::set_error_handler, metrics::MeterProvider, KeyValue};
use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use tokio::{net::TcpListener, runtime::Handle};

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

    let meter = metrics.meter("oak_functions_containers_app");
    let _tokio_metrics = [
        meter
            .u64_observable_counter("tokio_workers_count")
            .with_description("Number of worker threads used by the runtime")
            .with_callback(|counter| {
                if let Ok(num_workers) = Handle::current().metrics().num_workers().try_into() {
                    counter.observe(num_workers, &[]);
                }
            })
            .try_init()?,
        meter
            .u64_observable_counter("tokio_blocking_threads_count")
            .with_description("Number of additional threads used by the runtime")
            .with_callback(|counter| {
                if let Ok(num_blocking_threads) = Handle::current()
                    .metrics()
                    .num_blocking_threads()
                    .try_into()
                {
                    counter.observe(num_blocking_threads, &[]);
                }
            })
            .try_init()?,
        meter
            .u64_observable_counter("tokio_active_tasks")
            .with_description("Number of active tasks in the runtime")
            .with_callback(|counter| {
                if let Ok(active_tasks_count) =
                    Handle::current().metrics().active_tasks_count().try_into()
                {
                    counter.observe(active_tasks_count, &[]);
                }
            })
            .try_init()?,
        meter
            .u64_observable_counter("tokio_injection_queue_depth")
            .with_description("Number of tasks currently in the runtime's injection queue")
            .with_callback(|counter| {
                if let Ok(injection_queue_depth) = Handle::current()
                    .metrics()
                    .injection_queue_depth()
                    .try_into()
                {
                    counter.observe(injection_queue_depth, &[]);
                }
            })
            .try_init()?,
        meter
            .u64_observable_counter("tokio_worker_local_queue_depth")
            .with_description("Number of tasks currently scheduled in the workers' local queue")
            .with_callback(|counter| {
                let metrics = Handle::current().metrics();
                for worker in 0..metrics.num_workers() {
                    if let (Ok(depth), Ok(worker)) = (
                        metrics.worker_local_queue_depth(worker).try_into(),
                        worker.try_into(),
                    ) {
                        counter.observe(depth, &[KeyValue::new::<&str, i64>("worker", worker)])
                    }
                }
            })
            .try_init()?,
    ];

    let mut client = OrchestratorClient::create()
        .await
        .context("couldn't create Orchestrator client")?;
    let encryption_key_handle = InstanceEncryptionKeyHandle::create()
        .await
        .map_err(|error| anyhow!("couldn't create encryption key handle: {:?}", error))?;

    // To be used when connecting trusted app to orchestrator.
    let _application_config = client.get_application_config().await?;

    let addr = SocketAddr::new(
        IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        OAK_FUNCTIONS_CONTAINERS_APP_PORT,
    );
    let listener = TcpListener::bind(addr).await?;
    let server_handle = tokio::spawn(serve(listener, Arc::new(encryption_key_handle), meter));

    eprintln!("Running Oak Functions on Oak Containers at address: {addr}");
    client.notify_app_ready().await?;
    Ok(server_handle.await??)
}
