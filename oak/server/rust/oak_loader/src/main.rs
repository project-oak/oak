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

use log::info;
use oak_runtime::{configure_and_run, proto::oak::application::ApplicationConfiguration};
use prost::Message;
use std::{fs::File, io::Read, thread::park};
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
    env_logger::init();
    info!("Loading Oak Runtime");

    let opt = Opt::from_args();
    let app_config = {
        let buffer = read_file(&opt.application)?;
        ApplicationConfiguration::decode(&buffer[..])
            .map_err(|error| format!("Failed to decode application configuration: {:?}", error))?
    };

    // Spawns a new thread corresponding to an initial Wasm Oak node.
    configure_and_run(app_config).map_err(|error| format!("Runtime error: {:?}", error))?;
    // Park current thread.
    park();

    Ok(())
}
