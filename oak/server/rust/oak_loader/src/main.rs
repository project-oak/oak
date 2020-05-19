//
// Copyright 2020 The Project Oak Authors
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

//! An utility binary to run Oak Runtime.
//!
//! To invoke, run the following command from the root of the repository:
//!
//! cargo run --package=oak_loader -- \
//!     --application=<APP_CONFIG_PATH> \
//!     --grpc-tls-private-key=<PRIVATE_KEY_PATH> \
//!     --grpc-tls-certificate=<CERTIFICATE_PATH> \
//!     --root-tls-certificate=<CERTIFICATE_PATH>

use anyhow::anyhow;
use core::str::FromStr;
use log::{debug, info};
use oak_runtime::{configure_and_run, proto::oak::application::ApplicationConfiguration};
use prost::Message;
use std::{
    collections::HashMap,
    fs::{read_to_string, File},
    io::Read,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};
use structopt::StructOpt;

#[cfg(test)]
mod tests;

use oak_runtime::proto::oak::application::{
    node_configuration::ConfigType::{GrpcClientConfig, GrpcServerConfig},
    ConfigMap,
};

#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Loader")]
pub struct Opt {
    #[structopt(long, help = "Application configuration file.")]
    application: String,
    #[structopt(long, help = "Private RSA key file used by gRPC server pseudo-Nodes.")]
    grpc_tls_private_key: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by gRPC server pseudo-Nodes."
    )]
    grpc_tls_certificate: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC service."
    )]
    root_tls_certificate: String,
    #[structopt(long, default_value = "3030", help = "Metrics server port number.")]
    metrics_port: u16,
    #[structopt(long, help = "Starts the Runtime without a metrics server.")]
    no_metrics: bool,
    #[structopt(
        long,
        default_value = "1909",
        help = "Introspection server port number."
    )]
    introspect_port: u16,
    #[structopt(long, help = "Starts the Runtime without an introspection server.")]
    no_introspect: bool,
    #[structopt(
        long,
        help = "Configuration files to expose to the Oak Application, each in key=filename format."
    )]
    config_files: Vec<ConfigEntry>,
}

/// A specification of a configuration entry as human readable key and a path to a file whose
/// contents constitutes the actual value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigEntry {
    key: String,
    filename: String,
}

impl FromStr for ConfigEntry {
    type Err = anyhow::Error;
    fn from_str(v: &str) -> Result<Self, Self::Err> {
        let parts = v.split('=').collect::<Vec<_>>();
        if parts.len() != 2 {
            return Err(anyhow!("could not parse config entry: {}", v));
        }
        Ok(ConfigEntry {
            key: parts[0].to_string(),
            filename: parts[1].to_string(),
        })
    }
}

fn read_file(filename: &str) -> anyhow::Result<Vec<u8>> {
    let mut file = File::open(filename)
        .map_err(|error| anyhow!("Failed to open file <{}>: {:?}", filename, error))?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)
        .map_err(|error| anyhow!("Failed to read file <{}>: {:?}", filename, error))?;
    Ok(buffer)
}

fn parse_config_files(config_entries: &[ConfigEntry]) -> anyhow::Result<HashMap<String, Vec<u8>>> {
    let mut file_map = HashMap::new();
    for config_entry in config_entries {
        if file_map.contains_key(&config_entry.key) {
            return Err(anyhow!("duplicate config entry key: {}", config_entry.key));
        }
        let file_content = read_file(&config_entry.filename)?;
        file_map.insert(config_entry.key.to_string(), file_content);
    }
    Ok(file_map)
}

pub fn parse_config_map(config_files: &[ConfigEntry]) -> anyhow::Result<ConfigMap> {
    Ok(ConfigMap {
        items: parse_config_files(config_files)?,
    })
}

fn main() -> anyhow::Result<()> {
    if cfg!(feature = "oak_debug") {
        simple_logger::init_by_env();
    } else {
        eprintln!("No debugging output configured at build time");
    }
    let opt = Opt::from_args();
    debug!("parsed opts: {:?}", opt);

    let config_map = parse_config_map(&opt.config_files)?;
    // We only log the keys here, since the values may be secret.
    debug!("parsed config map entries: {:?}", config_map.items.keys());
    // TODO(#689): Pass the `config_map` object to the Runtime instance, and make it available to
    // the running Oak Application.

    // Load application configuration.
    let app_config_data = read_file(&opt.application)?;
    let mut app_config = ApplicationConfiguration::decode(app_config_data.as_ref())?;

    // Assign a TLS identity to all gRPC server and client nodes in the application configuration.
    let grpc_tls_private_key = read_to_string(&opt.grpc_tls_private_key)?;
    let grpc_tls_certificate = read_to_string(&opt.grpc_tls_certificate)?;
    let root_tls_certificate = read_to_string(&opt.root_tls_certificate)?;
    for node in &mut app_config.node_configs {
        if let Some(GrpcServerConfig(ref mut grpc_server_config)) = node.config_type {
            grpc_server_config.grpc_tls_private_key = grpc_tls_private_key.clone();
            grpc_server_config.grpc_tls_certificate = grpc_tls_certificate.clone();
        } else if let Some(GrpcClientConfig(ref mut grpc_client_config)) = node.config_type {
            grpc_client_config.root_tls_certificate = root_tls_certificate.clone();
        }
    }

    // Create Runtime config.
    #[cfg(feature = "oak_debug")]
    let runtime_config = oak_runtime::RuntimeConfiguration {
        metrics_port: if opt.no_metrics {
            None
        } else {
            Some(opt.metrics_port)
        },
        introspect_port: if opt.no_introspect {
            None
        } else {
            Some(opt.introspect_port)
        },
    };
    #[cfg(not(feature = "oak_debug"))]
    let runtime_config = oak_runtime::RuntimeConfiguration {
        metrics_port: None,
        introspect_port: None,
    };

    // Start the Runtime from the given config.
    info!("starting Runtime, config {:?}", runtime_config);
    let (runtime, initial_handle) = configure_and_run(app_config, runtime_config)
        .map_err(|status| anyhow!("status {:?}", status))?;
    info!(
        "initial node {:?} with write handle {:?}",
        runtime.node_id, initial_handle
    );

    let done = Arc::new(AtomicBool::new(false));
    signal_hook::flag::register(signal_hook::SIGINT, Arc::clone(&done))?;

    // The Runtime kicks off its own threads for the initial Node and any subsequently created
    // Nodes, so just block the current thread until a signal arrives.
    while !done.load(Ordering::Relaxed) {
        // There are few synchronization mechanisms that are allowed to be used in a signal
        // handler context, so use a primitive sleep loop to watch for the termination
        // notification (rather than something more accurate like `std::sync::Condvar`).
        // See e.g.: http://man7.org/linux/man-pages/man7/signal-safety.7.html
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    info!("stop Runtime");
    runtime.stop_runtime();

    info!("Runtime stopped");
    Ok(())
}
