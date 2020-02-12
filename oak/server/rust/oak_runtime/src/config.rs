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

use crate::proto::manager::{
    ApplicationConfiguration, LogConfiguration, NodeConfiguration, WebAssemblyConfiguration,
};
use itertools::Itertools;
use std::collections::HashMap;

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
