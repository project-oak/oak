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

use std::{
    error::Error,
    fmt::Display,
    net::{IpAddr, Ipv4Addr, SocketAddr},
    num::{NonZeroU16, NonZeroU32},
    sync::Arc,
    time::Duration,
};

use anyhow::{anyhow, Context};
use clap::Parser;
use oak_containers_orchestrator::launcher_client::LauncherClient;
use oak_containers_sdk::{InstanceEncryptionKeyHandle, OrchestratorClient};
use oak_crypto::encryption_key::AsyncEncryptionKeyHandle;
#[cfg(feature = "native")]
use oak_functions_containers_app::native_handler::NativeHandler;
use oak_functions_containers_app::serve as app_serve;
use oak_functions_service::{
    proto::oak::functions::config::{
        application_config::CommunicationChannel, ApplicationConfig, HandlerType,
        TcpCommunicationChannel, WasmtimeConfig,
    },
    wasm::wasmtime::WasmtimeHandler,
};
use opentelemetry::{
    global::set_error_handler,
    metrics::{Meter, MeterProvider},
    KeyValue,
};
use prost::Message;
use tokio::{
    io::{AsyncRead, AsyncWrite},
    net::TcpListener,
    runtime::Handle,
};
use tokio_stream::wrappers::TcpListenerStream;
use tokio_vsock::{VsockAddr, VsockListener};
use tonic::transport::server::Connected;

const OAK_FUNCTIONS_CONTAINERS_APP_PORT: u16 = 8080;

#[global_allocator]
static ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,
}

async fn serve<S>(
    addr: S,
    handler_type: HandlerType,
    handler_config: Option<WasmtimeConfig>,
    stream: Box<
        dyn tokio_stream::Stream<
                Item = Result<
                    impl Connected + AsyncRead + AsyncWrite + Send + Unpin + 'static,
                    impl Error + Send + Sync + 'static,
                >,
            > + Send
            + Unpin,
    >,
    encryption_key_handle: Box<dyn AsyncEncryptionKeyHandle + Send + Sync>,
    meter: Meter,
) -> anyhow::Result<()>
where
    S: Display,
{
    eprintln!("Running Oak Functions on Oak Containers at address: {addr}");

    match handler_type {
        HandlerType::HandlerUnspecified | HandlerType::HandlerWasm => {
            app_serve::<WasmtimeHandler>(
                stream,
                encryption_key_handle,
                meter,
                handler_config.unwrap_or_default(),
            )
            .await
        }
        HandlerType::HandlerNative => {
            if cfg!(feature = "native") {
                app_serve::<NativeHandler>(stream, encryption_key_handle, meter, ()).await
            } else {
                panic!(
                    "Application config specified `native` handler type, but this binary does not support that feature"
                );
            }
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let launcher_client = Arc::new(
        LauncherClient::create(args.launcher_addr.parse()?)
            .await
            .map_err(|error| anyhow!("couldn't create client: {:?}", error))?,
    );

    // Use eprintln here, as normal logging would go through the OTLP connection,
    // which may no longer be valid.
    set_error_handler(|err| eprintln!("oak_functions_containers_app: OTLP error: {}", err))?;

    // This is a hack to get _some_ logging out of the binary, and should be
    // replaced with proper OTLP logging (or logging to journald, or something) in
    // the not too distant future. Debug logging is also only enabled for the
    // `oak_functions_service` module as Tonic tends to be rather chatty if
    // you enable debug logs everywhere; also, this could end up in a feedback
    // loop as if we create a RPC do do the debug logging, it'll mean the RPC
    // itself will generate more debug logs, which in turn will be sent via a
    // RPC, and the cycle continues.
    stderrlog::new().module("oak_functions_service").verbosity(log::Level::Debug).init().unwrap();

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
                if let Ok(num_blocking_threads) =
                    Handle::current().metrics().num_blocking_threads().try_into()
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
                if let Ok(injection_queue_depth) =
                    Handle::current().metrics().injection_queue_depth().try_into()
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
                    if let (Ok(depth), Ok(worker)) =
                        (metrics.worker_local_queue_depth(worker).try_into(), worker.try_into())
                    {
                        counter.observe(depth, &[KeyValue::new::<&str, i64>("worker", worker)])
                    }
                }
            })
            .try_init()?,
    ];

    let mut client =
        OrchestratorClient::create().await.context("couldn't create Orchestrator client")?;
    let encryption_key_handle = Box::new(
        InstanceEncryptionKeyHandle::create()
            .await
            .map_err(|error| anyhow!("couldn't create encryption key handle: {:?}", error))?,
    );

    // To be used when connecting trusted app to orchestrator.
    let application_config = {
        let bytes =
            client.get_application_config().await.context("failed to get application config")?;

        // If we don't get a config at all, treat it as if it had defaults. Otherwise,
        // try parsing the message and fail if it doesn't make sense.
        if bytes.is_empty() {
            ApplicationConfig::default()
        } else {
            ApplicationConfig::decode(&bytes[..])?
        }
    };

    let handler_type = application_config.handler_type();
    let wasmtime_config = application_config.wasmtime_config;
    let communication_channel = application_config
        .communication_channel
        .unwrap_or_else(|| CommunicationChannel::TcpChannel(TcpCommunicationChannel::default()));

    let server_handle = match communication_channel {
        CommunicationChannel::TcpChannel(config) => {
            let port = NonZeroU16::new(config.port.try_into()?)
                .map_or(OAK_FUNCTIONS_CONTAINERS_APP_PORT, Into::into);
            let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), port);
            let listener = TcpListener::bind(addr).await?;
            tokio::spawn(serve(
                addr,
                handler_type,
                wasmtime_config,
                Box::new(TcpListenerStream::new(listener)),
                encryption_key_handle,
                meter,
            ))
        }
        CommunicationChannel::VsockChannel(config) => {
            let port = NonZeroU32::new(config.port)
                .map_or(OAK_FUNCTIONS_CONTAINERS_APP_PORT.into(), Into::into);
            let addr = VsockAddr::new(tokio_vsock::VMADDR_CID_ANY, port);
            let listener = VsockListener::bind(addr)?;
            tokio::spawn(serve(
                addr,
                handler_type,
                wasmtime_config,
                Box::new(listener.incoming()),
                encryption_key_handle,
                meter,
            ))
        }
    };

    client.notify_app_ready().await.context("failed to notify that app is ready")?;

    Ok(server_handle.await??)
}
