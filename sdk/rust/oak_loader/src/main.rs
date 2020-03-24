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
use clap::{App, Arg, ArgMatches};
use oak_runtime::configure_and_run;
use oak_runtime::proto::ApplicationConfiguration;
use prost::Message;
use std::fs::File;
use std::io::Read;

fn get_arguments() -> ArgMatches<'static> {
    App::new("Oak Loader")
        .about("")
        .arg(
            Arg::with_name("application")
                .short("a")
                .long("application")
                .required(true)
                .takes_value(true)
                .value_name("APP_CONFIG_FILE")
                .help("Application configuration file"),
        )
        .arg(
            Arg::with_name("ca_cert")
                .long("ca_cert")
                .takes_value(true)
                .value_name("CA_CERT")
                .help("Path to the PEM-encoded CA root certificate"),
        )
        .arg(
            Arg::with_name("private_key")
                .long("private_key")
                .takes_value(true)
                .value_name("PRIVATE_KEY")
                .help("Path to the private key"),
        )
        .arg(
            Arg::with_name("cert_chain")
                .long("cert_chain")
                .takes_value(true)
                .value_name("CERT_CHAIN")
                .help("Path to the PEM-encoded certificate chain"),
        )
        .get_matches()
}

fn read_file(filename: &str) -> Result<Vec<u8>, String> {
    let mut file = File::open(filename).or_else(|e| format);
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let arguments = get_arguments();
    let app_config_path = arguments
        .value_of("application")
        .expect("Application configuration file is not specified");

    let app_config = {
        let mut file = File::open(app_config_path).expect("Config file not found");
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)?;
        ApplicationConfiguration::decode(&buffer[..])?
    };
    
    // TODO(#751): Implement TLS credentials for Rust Oak Runtime.
    configure_and_run(app_config).expect("Runtime error");

    Ok(())
}
