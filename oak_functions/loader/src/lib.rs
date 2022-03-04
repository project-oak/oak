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

#![feature(async_closure)]

pub mod grpc;
pub mod logger;
pub mod lookup;
pub mod lookup_data;
#[cfg(feature = "oak-metrics")]
pub mod metrics;
pub mod server;
#[cfg(feature = "oak-tf")]
pub mod tf;

#[cfg(feature = "oak-metrics")]
use crate::metrics::PrivateMetricsProxyFactory;
#[cfg(feature = "oak-tf")]
use crate::tf::{read_model_from_path, TensorFlowFactory};
use crate::{
    grpc::{create_and_start_grpc_server, create_wasm_handler},
    logger::Logger,
    lookup::LookupFactory,
    lookup_data::{LookupData, LookupDataAuth, LookupDataSource},
    server::Policy,
};
use anyhow::Context;
use clap::Parser;
use log::Level;
use oak_functions_abi::proto::{ConfigurationInfo, ServerPolicy};
#[cfg(feature = "oak-metrics")]
use oak_functions_metrics::PrivateMetricsConfig;
#[cfg(feature = "oak-tf")]
use oak_functions_tf_inference::TensorFlowModelConfig;
use oak_logger::OakLogger;
use oak_remote_attestation::crypto::get_sha256;
use serde_derive::Deserialize;
use std::{
    fs,
    net::{Ipv6Addr, SocketAddr},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::Duration,
};

#[cfg(test)]
mod tests;

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Config {
    /// URL of a file containing key / value entries in protobuf binary format for lookup.
    ///
    /// If empty or not provided, no data is available for lookup.
    #[serde(default)]
    lookup_data: Option<Data>,
    /// How often to refresh the lookup data.
    ///
    /// If empty or not provided, data is only loaded once at startup.
    #[serde(default, with = "humantime_serde")]
    lookup_data_download_period: Option<Duration>,
    /// Whether to use the GCP metadata service to obtain an authentication token for downloading
    /// the lookup data.
    #[serde(default = "LookupDataAuth::default")]
    lookup_data_auth: LookupDataAuth,
    /// Number of worker threads available to the async runtime.
    ///
    /// Defaults to 4 if unset.
    ///
    /// Note that the CPU core detection logic does not seem to work reliably on Google Cloud Run,
    /// so it is advisable to set this value to the number of cores available on the Cloud Run
    /// instance.
    ///
    /// See <https://docs.rs/tokio/1.5.0/tokio/runtime/struct.Builder.html#method.worker_threads>.
    worker_threads: Option<usize>,
    /// Security policy guaranteed by the server.
    policy: Option<Policy>,
    /// Configuration for TensorFlow model
    #[cfg(feature = "oak-tf")]
    #[serde(default)]
    tf_model: Option<TensorFlowModelConfig>,
    /// Differentially private metrics configuration.
    #[cfg(feature = "oak-metrics")]
    #[serde(default)]
    metrics: Option<PrivateMetricsConfig>,
}

#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
enum Data {
    /// Download data file via HTTP GET.
    /// Supported URL schemes: `http`, `https`.
    Url(String),
    /// Read data file from the local file system.
    /// File path is relative to the current `$PWD` (*not* relative to the config file).
    File(String),
}

/// Command line options for the Oak loader.
///
/// In general, when adding new configuration parameters, they should go in the `Config` struct
/// instead of here, and provided as part of the config TOML file by the developer, who would
/// normally bundle it with the Docker image of the Oak Functions Loader.
#[derive(Parser, Clone, Debug)]
#[clap(about = "Oak Functions Loader")]
pub struct Opt {
    #[clap(
        long,
        default_value = "8080",
        help = "Port number that the server listens on."
    )]
    http_listen_port: u16,
    #[clap(
        long,
        help = "Path to a Wasm file to be loaded and executed per invocation. The Wasm module must export a function named `main`."
    )]
    wasm_path: String,
    #[clap(
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

/// This crate is just a library so this function does not get executed directly by anything, it
/// needs to be wrapped in the "actual" `main` from a bin crate.
pub fn lib_main() -> anyhow::Result<()> {
    let opt = Opt::parse();
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

    #[allow(unused_mut)]
    let mut extensions = Vec::new();

    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data, logger.clone())?;
    extensions.push(lookup_factory);

    #[cfg(feature = "oak-tf")]
    if let Some(tf_model_config) = &config.tf_model {
        // Load the TensorFlow model from the given path in the config
        let model = read_model_from_path(&tf_model_config.path)?;
        let tf_model_factory = TensorFlowFactory::new_boxed_extension_factory(
            model,
            tf_model_config.shape.clone(),
            logger.clone(),
        )?;
        extensions.push(tf_model_factory);
    }

    #[cfg(feature = "oak-metrics")]
    if let Some(metrics_config) = &config.metrics {
        let metrics_factory = PrivateMetricsProxyFactory::new_boxed_extension_factory(
            metrics_config,
            logger.clone(),
        )?;
        extensions.push(metrics_factory);
    }

    let wasm_module_bytes = fs::read(&opt.wasm_path)
        .with_context(|| format!("Couldn't read Wasm file {}", &opt.wasm_path))?;

    // Make sure that a policy is specified and is valid.
    let policy = config
        .policy
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("a valid policy must be provided"))
        .and_then(|policy| policy.validate())?;

    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, opt.http_listen_port));
    let tee_certificate = vec![];

    let wasm_handler = create_wasm_handler(&wasm_module_bytes, extensions, logger.clone())?;

    let config_info = get_config_info(&wasm_module_bytes, policy.clone(), &config)?;

    // Start server.
    let server_handle = tokio::spawn(async move {
        create_and_start_grpc_server(
            &address,
            wasm_handler,
            tee_certificate,
            policy.clone(),
            config_info,
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
    // arrives. This is needed for getting the correct status code when running with `xtask`.
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
    let lookup_data_source = match &config.lookup_data {
        Some(lookup_data) => match &lookup_data {
            Data::Url(url_string) => {
                let url = url::Url::parse(url_string).context("Couldn't parse lookup data URL")?;
                match url.scheme() {
                    "http" | "https" => Some(LookupDataSource::Http {
                        url: url_string.clone(),
                        auth: config.lookup_data_auth,
                    }),
                    scheme => anyhow::bail!(
                        "Unknown URL scheme in lookup data: expected 'http' or 'https', found {}",
                        scheme
                    ),
                }
            }
            Data::File(path) => Some(LookupDataSource::File(path.clone().into())),
        },
        None => None,
    };
    let lookup_data = Arc::new(LookupData::new_empty(
        lookup_data_source.clone(),
        logger.clone(),
    ));
    if lookup_data_source.is_some() {
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

#[allow(unused_variables)]
fn get_config_info(
    wasm_module_bytes: &[u8],
    policy: ServerPolicy,
    config: &Config,
) -> anyhow::Result<ConfigurationInfo> {
    #[cfg(feature = "oak-metrics")]
    let metrics = match &config.metrics {
        Some(ref metrics_config) => Some(oak_functions_abi::proto::PrivateMetricsConfig {
            epsilon: metrics_config.epsilon,
            batch_size: metrics_config
                .batch_size
                .try_into()
                .context("could not convert usize to u32")?,
        }),
        None => None,
    };
    #[cfg(not(feature = "oak-metrics"))]
    let metrics = None;

    #[cfg(feature = "oak-tf")]
    let ml_inference = config.tf_model.is_some();
    #[cfg(not(feature = "oak-tf"))]
    let ml_inference = false;

    Ok(ConfigurationInfo {
        wasm_hash: get_sha256(wasm_module_bytes).to_vec(),
        policy: Some(policy),
        ml_inference,
        metrics,
    })
}
