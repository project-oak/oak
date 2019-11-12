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
use oak_tests::proto::manager::{
    ApplicationConfiguration, Channel, Channel_Endpoint, GrpcServerNode, LogNode, Node,
    WebAssemblyNode,
};
use serial_test_derive::serial;
use std::collections::HashMap;

// Constants for node and port names that should match those in the textproto config
// held in ../../client/config.h.
const GRPC_NODE_NAME: &str = "grpc_server";
const FRONTEND_NODE_NAME: &str = "frontend";
const FRONTEND_CODE_NAME: &str = "frontend-code";
const BACKEND_NODE_NAME_PATTERN: &str = "backend_";
const BACKEND_CODE_NAME: &str = "backend-code";
const LOG_NODE_NAME: &str = "logging_node";
const GRPC_PORT_NAME: &str = "gRPC_input"; // deliberately non-default value
const FE_LOG_PORT: &str = "logging_port";
const FE_TO_BE_PORT_NAME_PATTERN: &str = "to_backend_";
const FE_FROM_BE_PORT_NAME_PATTERN: &str = "from_backend_";
const BE_FROM_FE_PORT_NAME: &str = "from_frontend";
const BE_TO_FE_PORT_NAME: &str = "to_frontend";
const BE_LOG_PORT: &str = "be_logging_port";

fn test_config() -> ApplicationConfiguration {
    let mut grpc = Node::new();
    grpc.set_node_name(GRPC_NODE_NAME.to_string());
    grpc.set_grpc_server_node(GrpcServerNode::new());
    let mut frontend = Node::new();
    frontend.set_node_name(FRONTEND_NODE_NAME.to_string());
    let mut wasm_node = WebAssemblyNode::new();
    wasm_node.set_wasm_contents_name(FRONTEND_CODE_NAME.to_string());
    frontend.set_web_assembly_node(wasm_node);
    let mut log = Node::new();
    log.set_node_name(LOG_NODE_NAME.to_string());
    log.set_log_node(LogNode::new());

    let mut grpc_channel = Channel::new();
    {
        let mut src_endpoint = Channel_Endpoint::new();
        src_endpoint.set_node_name(GRPC_NODE_NAME.to_string());
        src_endpoint.set_port_name(oak::grpc::OUT_PORT_NAME.to_string());
        grpc_channel.set_source_endpoint(src_endpoint);
        let mut dest_endpoint = Channel_Endpoint::new();
        dest_endpoint.set_node_name(FRONTEND_NODE_NAME.to_string());
        dest_endpoint.set_port_name(GRPC_PORT_NAME.to_string());
        grpc_channel.set_destination_endpoint(dest_endpoint);
    }
    let mut log_channel = Channel::new();
    {
        let mut src_endpoint = Channel_Endpoint::new();
        src_endpoint.set_node_name(FRONTEND_NODE_NAME.to_string());
        src_endpoint.set_port_name(FE_LOG_PORT.to_string());
        log_channel.set_source_endpoint(src_endpoint);
        let mut dest_endpoint = Channel_Endpoint::new();
        dest_endpoint.set_node_name(LOG_NODE_NAME.to_string());
        dest_endpoint.set_port_name(oak_log::IN_PORT_NAME.to_string());
        log_channel.set_destination_endpoint(dest_endpoint);
    }

    let mut nodes = vec![grpc, frontend, log];
    let mut channels = vec![grpc_channel, log_channel];
    for i in 0..3 {
        let name = format!("{}{}", BACKEND_NODE_NAME_PATTERN, i);
        let mut backend = Node::new();
        backend.set_node_name(name.clone());
        let mut wasm_node = WebAssemblyNode::new();
        wasm_node.set_wasm_contents_name(BACKEND_CODE_NAME.to_string());
        backend.set_web_assembly_node(wasm_node);
        nodes.push(backend);

        {
            let mut channel = Channel::new();
            let mut src_endpoint = Channel_Endpoint::new();
            src_endpoint.set_node_name(FRONTEND_NODE_NAME.to_string());
            src_endpoint.set_port_name(format!("{}{}", FE_TO_BE_PORT_NAME_PATTERN, i));
            channel.set_source_endpoint(src_endpoint);
            let mut dest_endpoint = Channel_Endpoint::new();
            dest_endpoint.set_node_name(name.clone());
            dest_endpoint.set_port_name(BE_FROM_FE_PORT_NAME.to_string());
            channel.set_destination_endpoint(dest_endpoint);
            channels.push(channel);
        }
        {
            let mut channel = Channel::new();
            let mut src_endpoint = Channel_Endpoint::new();
            src_endpoint.set_node_name(name.clone());
            src_endpoint.set_port_name(BE_TO_FE_PORT_NAME.to_string());
            channel.set_source_endpoint(src_endpoint);
            let mut dest_endpoint = Channel_Endpoint::new();
            dest_endpoint.set_node_name(FRONTEND_NODE_NAME.to_string());
            dest_endpoint.set_port_name(format!("{}{}", FE_FROM_BE_PORT_NAME_PATTERN, i));
            channel.set_destination_endpoint(dest_endpoint);
            channels.push(channel);
        }
        {
            let mut log_channel = Channel::new();
            let mut src_endpoint = Channel_Endpoint::new();
            src_endpoint.set_node_name(name.clone());
            src_endpoint.set_port_name(BE_LOG_PORT.to_string());
            log_channel.set_source_endpoint(src_endpoint);
            let mut dest_endpoint = Channel_Endpoint::new();
            dest_endpoint.set_node_name(LOG_NODE_NAME.to_string());
            dest_endpoint.set_port_name(oak_log::IN_PORT_NAME.to_string());
            log_channel.set_destination_endpoint(dest_endpoint);
            channels.push(log_channel);
        }
    }

    let mut config = ApplicationConfiguration::new();
    config.set_nodes(protobuf::RepeatedField::from_vec(nodes));
    config.set_channels(protobuf::RepeatedField::from_vec(channels));
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
    entrypoints.insert("frontend-code".to_string(), fe);
    entrypoints.insert("backend-code".to_string(), be);
    oak_tests::start(test_config(), entrypoints);

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
