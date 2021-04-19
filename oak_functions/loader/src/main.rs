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
use prost::Message;
use serde_derive::Deserialize;
use std::{
    collections::HashMap,
    fs,
    net::{Ipv6Addr, SocketAddr},
    sync::{Arc, RwLock},
    time::{Duration, Instant},
};
use structopt::StructOpt;

use std::sync::atomic::{AtomicBool, Ordering};

mod logger;
mod server;
use crate::{logger::Logger, server::create_and_start_server};

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

struct LookupData {
    lookup_data_url: String,
    entries: RwLock<HashMap<Vec<u8>, Vec<u8>>>,
    logger: Logger,
}

impl LookupData {
    /// Creates a new [`LookupData`] instance that can refresh its internal entries from the
    /// provided data file URL.
    ///
    /// Entries in the data file path must be consecutive binary encoded and length delimited
    /// protobuf messages according to the definition in `/oak_functions/proto/lookup_data.proto`.
    ///
    /// The returned instance is empty, and must be populated by calling the [`LookupData::refresh`]
    /// method at least once.
    fn new_empty(lookup_data_url: &str, logger: Logger) -> LookupData {
        LookupData {
            lookup_data_url: lookup_data_url.to_string(),
            entries: RwLock::new(HashMap::new()),
            logger,
        }
    }

    /// Refreshes the internal entries of this struct from the data file URL provided at
    /// construction time.
    ///
    /// If successful, entries are completely replaced (i.e. not merged).
    ///
    /// If there is any error while reading or parsing the data, an error is returned by this
    /// method, and existing entries are left untouched. The caller may retry the refresh operation
    /// at a future time.
    async fn refresh(&self) -> anyhow::Result<()> {
        // TODO(#1930): Avoid loading the entire file in memory for parsing.
        let client = hyper::Client::new();
        let res = client
            .get(
                self.lookup_data_url
                    .parse()
                    .context("could not parse lookup data URL")?,
            )
            .await
            .context("could not fetch lookup data")?;

        let start = Instant::now();
        let lookup_data_buf = hyper::body::to_bytes(res.into_body())
            .await
            .context("could not read lookup data response body")?;
        self.logger.log_public(
            Level::Debug,
            &format!("lookup data download time: {:?}", start.elapsed()),
        );

        let start = Instant::now();
        let entries = parse_lookup_entries(&mut lookup_data_buf.as_ref())
            .context("could not parse lookup data")?;

        self.logger.log_public(
            Level::Info,
            &format!("loaded {} entries of lookup data", entries.len()),
        );
        self.logger.log_public(
            Level::Debug,
            &format!("lookup data parsing time: {:?}", start.elapsed()),
        );

        // This block is here to emphasize and ensure that the write lock is only held for a very
        // short time.
        let start = Instant::now();
        {
            *self
                .entries
                .write()
                .expect("could not lock entries for write") = entries;
        }
        self.logger.log_public(
            Level::Debug,
            &format!(
                "lookup data write lock acquisition time: {:?}",
                start.elapsed()
            ),
        );

        Ok(())
    }

    /// Convenience getter for an individual entry that reduces lock contention by cloning the
    /// resulting value as quickly as possible and returning it instead of a reference.
    #[allow(dead_code)]
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .get(key)
            .cloned()
    }

    #[allow(dead_code)]
    fn len(&self) -> usize {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .len()
    }
}

fn parse_lookup_entries<B: bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry =
            oak_functions_abi::proto::Entry::decode_length_delimited(&mut lookup_data_buffer)
                .context("could not decode entry")?;
        entries.insert(entry.key, entry.value);
    }
    Ok(entries)
}

async fn background_refresh_lookup_data(lookup_data: &LookupData, period: Duration) {
    // Create an interval that starts after `period`, since the data was already refreshed
    // initially.
    let mut interval = tokio::time::interval_at(tokio::time::Instant::now() + period, period);
    loop {
        interval.tick().await;
        // If there is an error, we skip the current refresh and wait for the next tick.
        if let Err(err) = lookup_data.refresh().await {
            lookup_data.logger.log_public(
                Level::Error,
                &format!("error refreshing lookup data: {}", err),
            );
        }
    }
}

/// Main execution point for the Oak Functions Loader.
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // TODO(#1971): Make maximum log level configurable.
    let logger = Logger::default();

    let opt = Opt::from_args();

    let config_file_bytes = fs::read(&opt.config_path)
        .with_context(|| format!("Couldn't read config file {}", &opt.config_path))?;
    let config: Config =
        toml::from_slice(&config_file_bytes).context("Couldn't parse config file")?;

    logger.log_public(Level::Info, &format!("parsed config file:\n{:#?}", config));

    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let _lookup_data = load_lookup_data(&config, logger.clone()).await?;

    // TODO(#1930): Pass lookup data to the server instance.

    // Start HTTP server.
    let wasm_module_bytes = fs::read(&opt.wasm_path)
        .with_context(|| format!("Couldn't read Wasm file {}", &opt.wasm_path))?;

    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.http_listen_port));
    let server_handle = tokio::spawn(async move {
        create_and_start_server(&address, &wasm_module_bytes, notify_receiver, logger)
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
    let lookup_data = Arc::new(LookupData::new_empty(&config.lookup_data_url, logger));
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
            tokio::spawn(async move {
                background_refresh_lookup_data(&lookup_data, lookup_data_download_period).await
            });
        };
    }
    Ok(lookup_data)
}
