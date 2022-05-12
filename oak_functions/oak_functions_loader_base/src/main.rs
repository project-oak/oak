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
use oak_functions_loader::{logger::Logger, Config, LookupDataConfig, Opt};
use oak_logger::OakLogger;

use std::fs;

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
        LookupDataConfig {
            lookup_data: config.lookup_data,
            lookup_data_download_period: config.lookup_data_download_period,
            lookup_data_auth: config.lookup_data_auth,
        },
        config.worker_threads,
        config.policy,
        extension_factories,
        None,
    )
}
