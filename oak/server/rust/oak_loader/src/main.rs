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
//!     --grpc-tls-certificate=<CERTIFICATE_PATH>

use log::info;
use oak_runtime::{configure_and_run, proto::oak::application::ApplicationConfiguration};
use prost::Message;
use std::{
    fs::File,
    io::Read,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};
use structopt::StructOpt;

use oak_runtime::proto::oak::application::node_configuration::ConfigType::GrpcServerConfig;

#[derive(StructOpt, Clone)]
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
}

fn read_file(filename: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut file = File::open(filename)
        .map_err(|error| format!("Failed to open file <{}>: {:?}", filename, error))?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)
        .map_err(|error| format!("Failed to read file <{}>: {:?}", filename, error))?;
    Ok(buffer)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    if cfg!(feature = "oak_debug") {
        simple_logger::init_by_env();
    } else {
        eprintln!("No debugging output configured at build time");
    }
    let opt = Opt::from_args();

    // Load application configuration.
    let app_config_data = read_file(&opt.application)?;
    let mut app_config = ApplicationConfiguration::decode(app_config_data.as_ref())?;

    // Assign a TLS identity to all gRPC server nodes in the application configuration.
    let grpc_tls_private_key = read_file(&opt.grpc_tls_private_key)?;
    let grpc_tls_certificate = read_file(&opt.grpc_tls_certificate)?;
    for node in &mut app_config.node_configs {
        if let Some(GrpcServerConfig(ref mut grpc_server_config)) = node.config_type {
            grpc_server_config.grpc_tls_private_key = grpc_tls_private_key.clone();
            grpc_server_config.grpc_tls_certificate = grpc_tls_certificate.clone();
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
        .map_err(|status| format!("status {:?}", status))?;
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
