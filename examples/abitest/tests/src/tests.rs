//
// Copyright 2019 The Project Oak Authors
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

use abitest_frontend::proto::abitest::{ABITestRequest, ABITestResponse};
use assert_matches::assert_matches;
use log::{error, info};
use oak::grpc;
use oak::OakStatus;
use oak_runtime::proto::manager::{
    ApplicationConfiguration, LogConfiguration, NodeConfiguration, WebAssemblyConfiguration,
};
use serial_test_derive::serial;
use std::collections::HashMap;

// Constants for Node config names that should match those in the textproto
// config held in ../../client/config.h.
const FRONTEND_CONFIG_NAME: &str = "frontend-config";
const BACKEND_CONFIG_NAME: &str = "backend-config";
const LOG_CONFIG_NAME: &str = "logging-config";

fn test_config() -> ApplicationConfiguration {
    let mut frontend_config = NodeConfiguration::new();
    frontend_config.set_name(FRONTEND_CONFIG_NAME.to_string());
    frontend_config.set_wasm_config(WebAssemblyConfiguration::new());
    let mut backend_config = NodeConfiguration::new();
    backend_config.set_name(BACKEND_CONFIG_NAME.to_string());
    backend_config.set_wasm_config(WebAssemblyConfiguration::new());
    let mut log_config = NodeConfiguration::new();
    log_config.set_name(LOG_CONFIG_NAME.to_string());
    log_config.set_log_config(LogConfiguration::new());

    let mut config = ApplicationConfiguration::new();
    config.set_node_configs(protobuf::RepeatedField::from_vec(vec![
        frontend_config,
        backend_config,
        log_config,
    ]));
    config.set_initial_node(FRONTEND_CONFIG_NAME.to_string());
    config
}

#[test]
#[serial(node_test)]
fn test_abi() {
    // Initialize the test logger first, so logging gets redirected to simple_logger.
    // (A subsequent attempt to use the oak_log crate will fail.)
    oak_tests::init_logging();
    let mut entrypoints = HashMap::new();
    let fe: oak_tests::NodeMain = abitest_frontend::main;
    let be: oak_tests::NodeMain = abitest_backend::main;
    entrypoints.insert(FRONTEND_CONFIG_NAME.to_string(), fe);
    entrypoints.insert(BACKEND_CONFIG_NAME.to_string(), be);
    assert_eq!(Some(()), oak_tests::start(test_config(), entrypoints));

    let mut req = ABITestRequest::new();
    // Skip raw tests (which use invalid memory addresses etc.).
    req.exclude = "Raw".to_string();
    let result: grpc::Result<ABITestResponse> =
        oak_tests::inject_grpc_request("/oak.examples.abitest.OakABITestService/RunTests", req);
    assert_matches!(result, Ok(_));

    assert_eq!(OakStatus::ERR_TERMINATED, oak_tests::stop());

    for result in result.unwrap().get_results() {
        info!(
            "[ {} ] {}",
            if result.success { " OK " } else { "FAIL" },
            result.name
        );
        if !result.success {
            error!("Failure details: {}", result.details);
        }
        assert_eq!(true, result.success);
    }
}
