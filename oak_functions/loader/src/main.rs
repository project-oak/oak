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

mod logger;
mod lookup;
mod server;
use crate::{logger::Logger, lookup::LookupData, server::create_and_start_server};

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

/// Main execution point for the Oak Functions Loader.
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();

    let config_file_bytes = fs::read(&opt.config_path)
        .with_context(|| format!("Couldn't read config file {}", &opt.config_path))?;
    let config: Config =
        toml::from_slice(&config_file_bytes).context("Couldn't parse config file")?;
    // Print the parsed config to STDERR regardless of whether the logger is initialized.

    // TODO(#1971): Make maximum log level configurable.
    let logger = Logger::default();

    logger.log_public(Level::Info, &format!("parsed config file:\n{:#?}", config));

    // For now the server runs in the same thread, so `notify_sender` is not really needed.
    let (_notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let wasm_module_bytes = fs::read(&opt.wasm_path)
        .with_context(|| format!("Couldn't read Wasm file {}", &opt.wasm_path))?;

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

    // TODO(#1930): Pass lookup data to the server instance.

    // Start HTTP server.
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.http_listen_port));
    create_and_start_server(
        &address,
        &wasm_module_bytes,
        lookup_data,
        notify_receiver,
        logger,
    )
    .await
}
