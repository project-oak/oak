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

//! The "unsafe" Oak Functions runtime binary, which does not guarantee that data stays private.
//!
//! Useful for testing and debugging, but not meant for production use.

use anyhow::Context;
use clap::Parser;
use log::Level;
use oak_functions_loader::{
    logger::Logger, Config, ExtensionConfigurationInfo, LookupDataConfig, Opt,
};
use oak_functions_metrics::PrivateMetricsProxyFactory;
use oak_functions_tf_inference::{read_model_from_path, TensorFlowFactory};
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

    let mut extension_factories = vec![];

    if let Some(tf_model_config) = &config.tf_model {
        // Load the TensorFlow model from the given path in the config
        let model = read_model_from_path(&tf_model_config.path)?;
        let tf_model_factory = TensorFlowFactory::new_boxed_extension_factory(
            model,
            tf_model_config.shape.clone(),
            logger.clone(),
        )?;
        extension_factories.push(tf_model_factory);
        logger.log_public(Level::Info, "Added TensorFlow extension.");
    }

    if let Some(metrics_config) = &config.metrics {
        let metrics_factory = PrivateMetricsProxyFactory::new_boxed_extension_factory(
            metrics_config,
            logger.clone(),
        )?;
        extension_factories.push(metrics_factory);
        logger.log_public(Level::Info, "Added Metrics extension.");
    }

    let extension_configuration_info = get_extension_config_info(&config)?;

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
        Some(extension_configuration_info),
    )
}

fn get_extension_config_info(config: &Config) -> anyhow::Result<ExtensionConfigurationInfo> {
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

    let ml_inference = config.tf_model.is_some();

    Ok(ExtensionConfigurationInfo {
        ml_inference,
        metrics,
    })
}
