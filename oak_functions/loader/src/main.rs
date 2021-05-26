//
// Copyright 2021 The Project Oak Authors
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

// Required for enabling benchmark tests.
#![feature(test)]
#![feature(async_closure)]

use anyhow::Context;
use log::Level;
use serde_derive::Deserialize;
use std::{
    fs,
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use structopt::StructOpt;

use std::sync::atomic::{AtomicBool, Ordering};

mod grpc;
mod logger;
mod lookup;
mod server;
use crate::{grpc::create_and_start_grpc_server, logger::Logger, lookup::LookupData};
use server::Policy;

#[cfg(test)]
mod tests;
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Config {
    /// URL of a file to GET over HTTP containing key / value entries in protobuf binary format for
    /// lookup. If empty or not provided, no data is available for lookup.
    #[serde(default)]
    lookup_data_url: String,
    /// How often to refresh the lookup data. If not provided, data is only loaded once at startup.
    #[serde(with = "humantime_serde")]
    lookup_data_download_period: Option<Duration>,
    /// Number of worker threads available to the async runtime.
    ///
    /// Defaults to 4 if unset.
    ///
    /// Note that the CPU core detection logic does not seem to work reliably on Google Cloud Run,
    /// so it is advisable to set this value to the number of cores available on the Cloud Run
    /// instance.
    ///
    /// See https://docs.rs/tokio/1.5.0/tokio/runtime/struct.Builder.html#method.worker_threads.
    worker_threads: Option<usize>,
    /// Path to a PEM encoded X.509 certificate that signs TEE firmware key. This field must be
    /// specified.
    tee_certificate_path: String,
    /// Security policy guaranteed by the server.
    policy: Option<Policy>,
}

/// Command line options for the Oak loader.
///
/// In general, when adding new configuration parameters, they should go in the `Config` struct
/// instead of here, and provided as part of the config TOML file by the developer, who would
/// normally bundle it with the Docker image of the Oak Functions Loader.
#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Functions Loader")]
pub struct Opt {
    #[structopt(
        long,
        default_value = "8080",
        help = "Port number that the server listens on."
    )]
    http_listen_port: u16,
    #[structopt(
        long,
        help = "Path to a Wasm file to be loaded and executed per invocation. The Wasm module must export a function named `main`."
    )]
    wasm_path: String,
    #[structopt(
        long,
        help = "Path to a file containing configuration parameters in TOML format."
    )]
    config_path: String,
}

async fn background_refresh_lookup_data(
    lookup_data: &LookupData,
    period: Duration,
    logger: &Logger,
) {
    // Create an interval that starts after `period`, since the data was already refreshed
    // initially.
    let mut interval = tokio::time::interval_at(tokio::time::Instant::now() + period, period);
    loop {
        interval.tick().await;
        // If there is an error, we skip the current refresh and wait for the next tick.
        if let Err(err) = lookup_data.refresh().await {
            logger.log_public(
                Level::Error,
                &format!("error refreshing lookup data: {}", err),
            );
        }
    }
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();
    let config_file_bytes = fs::read(&opt.config_path)
        .with_context(|| format!("Couldn't read config file {}", &opt.config_path))?;
    let config: Config =
        toml::from_slice(&config_file_bytes).context("Couldn't parse config file")?;
    // TODO(#1971): Make maximum log level configurable.
    let logger = Logger::default();
    logger.log_public(Level::Info, &format!("parsed config file:\n{:#?}", config));
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(config.worker_threads.unwrap_or(4))
        .enable_all()
        .build()
        .unwrap()
        .block_on(async_main(opt, config, logger))
}

/// Main execution point for the Oak Functions Loader.
async fn async_main(opt: Opt, config: Config, logger: Logger) -> anyhow::Result<()> {
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let lookup_data = load_lookup_data(&config, logger.clone()).await?;

    let wasm_module_bytes = fs::read(&opt.wasm_path)
        .with_context(|| format!("Couldn't read Wasm file {}", &opt.wasm_path))?;

    // Make sure that a policy is specified and is valid.
    config
        .policy
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("a valid policy must be provided"))
        .and_then(|policy| policy.validate())?;

    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.http_listen_port));
    let tee_certificate =
        std::fs::read(&config.tee_certificate_path).context("Couldn't load certificate")?;

    // Start server.
    let server_handle = tokio::spawn(async move {
        create_and_start_grpc_server(
            &address,
            tee_certificate.to_vec(),
            &wasm_module_bytes,
            lookup_data,
            config.policy.unwrap(),
            async { notify_receiver.await.unwrap() },
            logger,
        )
        .await
        .context("error while waiting for the server to terminate")
    });

    // Wait for the termination signal.
    let done = Arc::new(AtomicBool::new(false));
    signal_hook::flag::register(signal_hook::consts::signal::SIGINT, Arc::clone(&done))
        .context("could not register signal handler")?;

    // The server is started in its own thread, so just block the current thread until a signal
    // arrives. This is needed for getting the correct status code when running with `runner`.
    while !done.load(Ordering::Relaxed) {
        // There are few synchronization mechanisms that are allowed to be used in a signal
        // handler context, so use a primitive sleep loop to watch for the termination
        // notification (rather than something more accurate like `std::sync::Condvar`).
        // See e.g.: http://man7.org/linux/man-pages/man7/signal-safety.7.html
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    notify_sender
        .send(())
        .expect("Couldn't send completion signal.");

    server_handle
        .await
        .context("error while waiting for the server to terminate")?
}

async fn load_lookup_data(config: &Config, logger: Logger) -> anyhow::Result<Arc<LookupData>> {
    let lookup_data = Arc::new(LookupData::new_empty(
        &config.lookup_data_url,
        logger.clone(),
    ));
    if !config.lookup_data_url.is_empty() {
        // First load the lookup data upfront in a blocking fashion.
        // TODO(#1930): Retry the initial lookup a few times if it fails.
        lookup_data
            .refresh()
            .await
            .context("Couldn't perform initial load of lookup data")?;
        if let Some(lookup_data_download_period) = config.lookup_data_download_period {
            // Create background task to periodically refresh the lookup data.
            let lookup_data = lookup_data.clone();
            let logger = logger.clone();
            tokio::spawn(async move {
                background_refresh_lookup_data(&lookup_data, lookup_data_download_period, &logger)
                    .await
            });
        };
    }
    Ok(lookup_data)
}
