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

use maplit::hashmap;

use oak_runtime::proto::oak::application::{
    node_configuration::ConfigType::{LogConfig, WasmConfig},
    ApplicationConfiguration, LogConfiguration, NodeConfiguration, WebAssemblyConfiguration,
};

#[test]
fn test_app_config() {
    let cfg = oak_runtime::application_configuration(
        hashmap!["node".to_string() => vec![0x00, 0x01]],
        "lumberjack",
        "node",
        "main",
    );
    assert_eq!(
        ApplicationConfiguration {
            node_configs: vec![
                NodeConfiguration {
                    name: "node".to_string(),
                    config_type: Some(WasmConfig(WebAssemblyConfiguration {
                        module_bytes: vec![0, 1]
                    }))
                },
                NodeConfiguration {
                    name: "lumberjack".to_string(),
                    config_type: Some(LogConfig(LogConfiguration {}))
                }
            ],
            initial_node_config_name: "node".to_string(),
            initial_entrypoint_name: "main".to_string(),
        },
        cfg
    );
}

#[test]
fn test_app_config_multi() {
    let cfg = oak_runtime::application_configuration(
        hashmap![
            "node".to_string() => vec![0x00, 0x01],
            "another_node".to_string() => vec![0x02, 0x03],
        ],
        "lumberjack",
        "node",
        "main",
    );
    assert_eq!(
        ApplicationConfiguration {
            node_configs: vec![
                NodeConfiguration {
                    name: "another_node".to_string(),
                    config_type: Some(WasmConfig(WebAssemblyConfiguration {
                        module_bytes: vec![2, 3]
                    }))
                },
                NodeConfiguration {
                    name: "node".to_string(),
                    config_type: Some(WasmConfig(WebAssemblyConfiguration {
                        module_bytes: vec![0, 1]
                    }))
                },
                NodeConfiguration {
                    name: "lumberjack".to_string(),
                    config_type: Some(LogConfig(LogConfiguration {}))
                }
            ],
            initial_node_config_name: "node".to_string(),
            initial_entrypoint_name: "main".to_string(),
        },
        cfg
    );
}

#[test]
fn test_app_config_no_logger() {
    let cfg = oak_runtime::application_configuration(
        hashmap!["node".to_string() => vec![0x00, 0x01]],
        "",
        "node",
        "main",
    );
    assert_eq!(
        ApplicationConfiguration {
            node_configs: vec![NodeConfiguration {
                name: "node".to_string(),
                config_type: Some(WasmConfig(WebAssemblyConfiguration {
                    module_bytes: vec![0, 1]
                }))
            },],
            initial_node_config_name: "node".to_string(),
            initial_entrypoint_name: "main".to_string(),
        },
        cfg
    );
}
