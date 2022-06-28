//
// Copyright 2022 The Project Oak Authors
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

//! The "base" Oak Functions runtime binary, which guarantees that user data stays private.

use anyhow::Context;
use clap::Parser;
use log::Level;
use oak_functions_loader::{logger::Logger, server::Policy, LoadLookupDataConfig, Opt};
use oak_logger::OakLogger;
use serde_derive::Deserialize;
use std::fs;

/// Runtime Configuration of Base Runtime.
///
/// This struct serves as a schema for a static TOML config file provided by
/// application developers. In deployment, this static config file is typically
/// bundled with the Oak Runtime binary. Config values captured in it serve
/// as a type safe version of regular command line flags.
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct Config {
    /// Configuration to load the LookupData.
    #[serde(default)]
    load_lookup_data: LoadLookupDataConfig,
    /// Security policy guaranteed by the server.
    policy: Option<Policy>,
}

pub fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();
    let config_file_bytes = fs::read(&opt.config_path)
        .with_context(|| format!("Couldn't read config file {}", &opt.config_path))?;
    let config: Config =
        toml::from_slice(&config_file_bytes).context("Couldn't parse config file")?;
    // TODO(#1971): Make maximum log level configurable.
    let logger = Logger::default();
    logger.log_public(Level::Info, &format!("parsed config file:\n{:#?}", config));

    let extension_factories = vec![];

    oak_functions_loader::lib_main(
        opt,
        logger,
        config.load_lookup_data,
        config.policy,
        extension_factories,
    )
}
