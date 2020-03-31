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

use crate::proto::{
    node_configuration::ConfigType, ApplicationConfiguration, LogConfiguration, NodeConfiguration,
    WebAssemblyConfiguration,
};
use itertools::Itertools;
use std::collections::HashMap;
use std::sync::Arc;

use log::error;

use oak_abi::OakStatus;

use crate::node;
use crate::node::load_wasm;
use crate::runtime;
use crate::runtime::{Handle, Runtime};

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
        .map(|(name, wasm)| NodeConfiguration {
            name,
            config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                module_bytes: wasm,
            })),
        })
        .collect();

    if !logger_name.is_empty() {
        nodes.push(NodeConfiguration {
            name: logger_name.to_string(),
            config_type: Some(ConfigType::LogConfig(LogConfiguration {})),
        });
    }

    ApplicationConfiguration {
        node_configs: nodes,
        initial_node_config_name: initial_node.into(),
        initial_entrypoint_name: entrypoint.into(),
        ..Default::default()
    }
}

/// Load a `runtime::Configuration` from a protobuf `ApplicationConfiguration`.
/// This can fail if an unsupported node is passed, or if a node was unable to be initialized with
/// the given configuration.
pub fn from_protobuf(
    app_config: ApplicationConfiguration,
) -> Result<runtime::Configuration, OakStatus> {
    let mut config = runtime::Configuration {
        nodes: HashMap::new(),
        entry_module: app_config.initial_node_config_name.clone(),
        entrypoint: app_config.initial_entrypoint_name.clone(),
    };

    for node in app_config.node_configs {
        config.nodes.insert(
            node.name.clone(),
            match &node.config_type {
                None => {
                    error!("Node config {} with no type", node.name);
                    return Err(OakStatus::ErrInvalidArgs);
                }
                Some(ConfigType::LogConfig(_)) => node::Configuration::LogNode,
                Some(ConfigType::WasmConfig(WebAssemblyConfiguration { module_bytes, .. })) => {
                    load_wasm(&module_bytes).map_err(|e| {
                        error!("Error loading Wasm module: {}", e);
                        OakStatus::ErrInvalidArgs
                    })?
                }
                Some(_) => {
                    error!("Pseudo-node not implemented!");
                    return Err(OakStatus::ErrInvalidArgs);
                }
            },
        );
    }

    Ok(config)
}

/// Configure a [`Runtime`] from the given protobuf [`ApplicationConfiguration`] and begin
/// execution. This returns a [`RuntimeRef`] reference to the created runtime, and a
/// writeable [`Handle`] to send messages into the runtime. Creating a new
/// channel and passing the write [`Handle`] into the runtime will enable messages to be
/// read back out from the [`Runtime`].
pub fn configure_and_run(
    app_config: ApplicationConfiguration,
) -> Result<(Arc<Runtime>, Handle), OakStatus> {
    let configuration = from_protobuf(app_config)?;
    let runtime = Arc::new(Runtime::create(configuration));
    let handle = runtime.clone().run()?;
    Ok((runtime, handle))
}
