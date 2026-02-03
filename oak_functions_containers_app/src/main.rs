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
    net::{IpAddr, Ipv6Addr, SocketAddr},
    num::{NonZeroU16, NonZeroU32},
};

use anyhow::Context;
use clap::Parser;
use oak_containers_agent::metrics::{MetricsConfig, OakObserver};
use oak_crypto::encryption_key::AsyncEncryptionKeyHandle;
use oak_functions_containers_app::serve as app_serve;
use oak_functions_service::wasm::wasmtime::WasmtimeHandler;
use oak_proto_rust::oak::functions::config::{
    ApplicationConfig, TcpCommunicationChannel, WasmtimeConfig,
    application_config::CommunicationChannel,
};
use oak_sdk_containers::{
    InstanceEncryptionKeyHandle, OrchestratorClient, default_orchestrator_channel,
};
use prost::Message;
use tokio::{
    io::{AsyncRead, AsyncWrite},
    net::TcpListener,
};
use tokio_stream::wrappers::TcpListenerStream;
use tokio_vsock::{VsockAddr, VsockListener};
use tonic::transport::server::Connected;

const OAK_FUNCTIONS_CONTAINERS_APP_PORT: u16 = 8080;

#[global_allocator]
static ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

#[derive(Parser, Debug)]
struct Args {
    #[arg(env, default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,
}

async fn serve<S>(
    addr: S,
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
    observer: OakObserver,
) -> anyhow::Result<()>
where
    S: Display,
{
    eprintln!("Running Oak Functions on Oak Containers at address: {addr}");

    app_serve::<WasmtimeHandler>(
        stream,
        encryption_key_handle,
        observer,
        handler_config.unwrap_or_default(),
    )
    .await
}

mod otel_logging {
    use tracing_subscriber::{filter::filter_fn, fmt::Layer, prelude::*};

    // Writes any opentelemetry errors to stderr.
    pub fn init() {
        let opentelemetry_layer = Layer::new()
            .with_writer(std::io::stderr.with_max_level(tracing::Level::WARN))
            .with_filter(filter_fn(|metadata| metadata.target().starts_with("opentelemetry")));

        tracing_subscriber::registry().with(opentelemetry_layer).init();
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    otel_logging::init();

    // This is a hack to get _some_ logging out of the binary, and should be
    // replaced with proper OTLP logging (or logging to journald, or something) in
    // the not too distant future. Debug logging is also only enabled for the
    // `oak_functions_service` module as Tonic tends to be rather chatty if
    // you enable debug logs everywhere; also, this could end up in a feedback
    // loop as if we create a RPC do do the debug logging, it'll mean the RPC
    // itself will generate more debug logs, which in turn will be sent via a
    // RPC, and the cycle continues.
    env_logger::builder()
        .filter_module("oak_functions_service", log::LevelFilter::Debug)
        .try_init()?;

    let metrics_config = MetricsConfig {
        launcher_addr: args.launcher_addr,
        scope: "oak_functions_containers_app",
        excluded_metrics: None,
    };

    let oak_observer = oak_containers_agent::metrics::init_metrics(metrics_config);

    let orchestrator_channel =
        default_orchestrator_channel().await.context("failed to create channel to orchestrator")?;

    let mut client = OrchestratorClient::create(&orchestrator_channel);
    let encryption_key_handle =
        Box::new(InstanceEncryptionKeyHandle::create(&orchestrator_channel));

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

    let wasmtime_config = application_config.wasmtime_config;
    let communication_channel = application_config
        .communication_channel
        .unwrap_or_else(|| CommunicationChannel::TcpChannel(TcpCommunicationChannel::default()));

    let server_handle = match communication_channel {
        CommunicationChannel::TcpChannel(config) => {
            let port = NonZeroU16::new(config.port.try_into()?)
                .map_or(OAK_FUNCTIONS_CONTAINERS_APP_PORT, Into::into);
            let addr = SocketAddr::new(IpAddr::V6(Ipv6Addr::UNSPECIFIED), port);
            let listener = TcpListener::bind(addr).await?;
            tokio::spawn(serve(
                addr,
                wasmtime_config,
                Box::new(TcpListenerStream::new(listener)),
                encryption_key_handle,
                oak_observer,
            ))
        }
        CommunicationChannel::VsockChannel(config) => {
            let port = NonZeroU32::new(config.port)
                .map_or(OAK_FUNCTIONS_CONTAINERS_APP_PORT.into(), Into::into);
            let addr = VsockAddr::new(tokio_vsock::VMADDR_CID_ANY, port);
            let listener = VsockListener::bind(addr)?;
            tokio::spawn(serve(
                addr,
                wasmtime_config,
                Box::new(listener.incoming()),
                encryption_key_handle,
                oak_observer,
            ))
        }
    };

    client.notify_app_ready().await.context("failed to notify that app is ready")?;

    Ok(server_handle.await??)
}
