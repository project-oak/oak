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
//! ```
//! cargo run --package=oak_loader -- --application=<APP_CONFIG_PATH>
//! ```

use log::{error, info};
use oak_runtime::{configure_and_run, proto::oak::application::ApplicationConfiguration};
use prost::Message;
use std::{fs::File, io::Read, thread};
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "Oak Loader")]
pub struct Opt {
    #[structopt(long, help = "Application configuration file")]
    application: String,
    // TODO(#806): Make arguments non-optional once TLS support is enabled.
    #[structopt(long, help = "Path to the PEM-encoded CA root certificate")]
    ca_cert: Option<String>,
    #[structopt(long, help = "Path to the private key")]
    private_key: Option<String>,
    #[structopt(long, help = "Path to the PEM-encoded certificate chain")]
    cert_chain: Option<String>,
    #[structopt(
        long,
        default_value = "3030",
        help = "Metrics server port number. Defaults to 3030."
    )]
    metrics_port: u16,
    #[structopt(long, help = "Starts the Runtime without a metrics server.")]
    no_metrics: bool,
    #[structopt(
        long,
        default_value = "1909",
        help = "Introspection server port number. Defaults to 1909."
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

fn start_runtime(
    application: String,
    runtime_config: oak_runtime::RuntimeConfiguration,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Loading Oak Runtime");

    let app_config = {
        let buffer = read_file(&application)?;
        ApplicationConfiguration::decode(&buffer[..])
            .map_err(|error| format!("Failed to decode application configuration: {:?}", error))?
    };

    // Start the Runtime from the given config.
    let (_runtime, _initial_handle) = configure_and_run(app_config, runtime_config)
        .map_err(|error| format!("Runtime error: {:?}", error))?;

    // The Runtime kicks off its own threads for the initial Node and any subsequently created
    // Nodes, so just park the current thread.
    thread::park();
    Ok(())
}

fn main() {
    env_logger::init();
    let opt = Opt::from_args();
    let application = opt.application.clone();

    // Start the runtime in a new thread
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

    if let Err(e) = start_runtime(application, runtime_config) {
        error!("failed to start Oak Runtime: {}", e);
    }
}
