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

use crate::proto::application::{
    ApplicationConfiguration, LogConfiguration, NodeConfiguration,
    NodeConfiguration_oneof_config_type, WebAssemblyConfiguration,
};
use itertools::Itertools;
use std::collections::HashMap;

use log::error;

use oak_abi::OakStatus;

use crate::channel::ChannelWriter;
use crate::node;
use crate::node::load_wasm;
use crate::runtime;
use crate::runtime::{Runtime, RuntimeRef};

/// Create an application configuration.
///
/// - module_name_wasm: collection of Wasm bytes indexed by config name.
/// - logger_name: Node name to use for a logger configuration; if empty no logger will be included.
/// - initial_node: Initial node to run on launch.
/// - entrypoint: Entrypoint in the initial node to run on launch.
pub fn application_configuration<S: ::std::hash::BuildHasher>(
    module_name_wasm: HashMap<String, Vec<u8>, S>,
    logger_name: &str,
    initial_node: &str,
    entrypoint: &str,
) -> ApplicationConfiguration {
    let mut nodes: Vec<NodeConfiguration> = module_name_wasm
        .into_iter()
        .sorted()
        .map(|(name, wasm)| {
            let mut node = NodeConfiguration::new();
            node.set_name(name);
            node.set_wasm_config({
                let mut w = WebAssemblyConfiguration::new();
                w.set_module_bytes(wasm);
                w
            });
            node
        })
        .collect();

    if !logger_name.is_empty() {
        nodes.push({
            let mut log_config = NodeConfiguration::new();
            log_config.set_name(logger_name.to_string());
            log_config.set_log_config(LogConfiguration::new());
            log_config
        });
    }

    ApplicationConfiguration {
        node_configs: nodes.into(),
        initial_node_config_name: initial_node.into(),
        initial_entrypoint_name: entrypoint.into(),
        ..Default::default()
    }
}

pub fn from_protobuf(
    app_config: ApplicationConfiguration,
) -> Result<runtime::Configuration, OakStatus> {
    let mut config = runtime::Configuration {
        nodes: HashMap::new(),
        entry_module: app_config.initial_node_config_name.clone(),
        entrypoint: app_config.initial_entrypoint_name.clone(),
    };

    for node in app_config.get_node_configs() {
        config.nodes.insert(
            node.name.clone(),
            match &node.config_type {
                None => {
                    error!("Node config {} with no type", node.name);
                    return Err(OakStatus::ERR_INVALID_ARGS);
                }
                Some(NodeConfiguration_oneof_config_type::log_config(_)) => {
                    node::Configuration::LogNode
                }
                Some(NodeConfiguration_oneof_config_type::wasm_config(
                    WebAssemblyConfiguration { module_bytes, .. },
                )) => load_wasm(&module_bytes).map_err(|e| {
                    error!("Error loading Wasm module: {}", e);
                    OakStatus::ERR_INVALID_ARGS
                })?,
                Some(_) => {
                    error!("Pseudo-node not implemented!");
                    return Err(OakStatus::ERR_INVALID_ARGS);
                }
            },
        );
    }

    Ok(config)
}

pub fn configure_and_run(
    app_config: ApplicationConfiguration,
) -> Result<(RuntimeRef, ChannelWriter), OakStatus> {
    let config = from_protobuf(app_config)?;
    Runtime::configure_and_run(config)
}
