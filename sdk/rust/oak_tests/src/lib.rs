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

//! Test utilities to help with unit testing of Oak SDK code.

use log::info;

use oak_runtime::ChannelEither;
use protobuf::{Message, ProtobufEnum};

use oak_runtime::proto::manager::{
    ApplicationConfiguration, LogConfiguration, NodeConfiguration, WebAssemblyConfiguration,
};

// TODO(#544)

/// Create a simple configuration with collection of Wasm nodes and a logger node.
///
/// - module_name_wasm: Node name and path to associated Wasm file.
/// - logger_name: Node name to use for a logger configuration.
/// - initial_node: Initial node to run on launch.
/// - entrypoint: Entrypoint in the initial node to run on launch.
// TODO(#563)
pub fn test_configuration<P: AsRef<std::path::Path>>(
    module_name_wasm: &[(&str, P)],
    logger_name: &str,
    initial_node: &str,
    entrypoint: &str,
) -> ApplicationConfiguration {
    let mut nodes: Vec<NodeConfiguration> = module_name_wasm
        .iter()
        .map(|(name, module)| {
            let wasm = std::fs::read(module).expect("Module missing");
            let mut node = NodeConfiguration::new();
            node.set_name(name.to_string());
            node.set_wasm_config({
                let mut w = WebAssemblyConfiguration::new();
                w.set_module_bytes(wasm);
                w
            });
            node
        })
        .collect();

    nodes.push({
        let mut log_config = NodeConfiguration::new();
        log_config.set_name(logger_name.to_string());
        log_config.set_log_config(LogConfiguration::new());
        log_config
    });

    let mut config = ApplicationConfiguration::new();
    config.set_node_configs(protobuf::RepeatedField::from_vec(nodes));
    config.set_initial_node_config_name(initial_node.to_string());
    config.set_initial_entrypoint_name(entrypoint.to_string());

    config
}

// TODO(#543)
pub fn grpc_request<R, Q>(
    channel: &oak_runtime::ChannelWriter,
    method_name: &str,
    req: R,
) -> oak::grpc::Result<Q>
where
    R: protobuf::Message,
    Q: protobuf::Message,
{
    // Put the request in a GrpcRequest wrapper and serialize into a message.
    let grpc_req = oak::grpc::encap_request(req, method_name).expect("failed to build GrpcRequest");
    let mut req_msg = oak_runtime::Message {
        data: vec![],
        channels: vec![],
    };

    grpc_req
        .write_to_writer(&mut req_msg.data)
        .expect("failed to serialize GrpcRequest message");

    // Create a new channel to hold the request message.
    let (req_write_half, req_read_half) = oak_runtime::channel::new();
    req_write_half
        .write(req_msg)
        .expect("could not write message");

    // Create a new channel for responses to arrive on and also attach that to the message.
    let (rsp_write_half, rsp_read_half) = oak_runtime::channel::new();

    // Create a notification message and attach the method-invocation specific channels to it.
    let notify_msg = oak_runtime::Message {
        data: vec![],
        channels: vec![
            ChannelEither::Reader(req_read_half),
            ChannelEither::Writer(rsp_write_half),
        ],
    };

    // Send the notification message (with attached handles) into the Node under test.
    channel.write(notify_msg).expect("could not write message");

    // Read the serialized, encapsulated response.
    loop {
        let rsp = match rsp_read_half.read() {
            Ok(Some(r)) => r,
            Ok(None) => {
                info!("no pending gRPC response message; poll again soon");
                std::thread::sleep(std::time::Duration::from_millis(100));
                continue;
            }
            Err(e) => {
                panic!("failed to read from response channel: {:?}", e);
            }
        };
        if rsp.data.is_empty() {
            info!("no pending message; poll again soon");
            std::thread::sleep(std::time::Duration::from_millis(100));
            continue;
        }
        let mut rsp: oak::proto::grpc_encap::GrpcResponse =
            protobuf::parse_from_bytes(&rsp.data).expect("failed to parse GrpcResponse message");
        if !rsp.last {
            panic!("Expected single final response");
        }

        if rsp.get_status().code != oak::grpc::Code::OK.value() {
            return Err(rsp.take_status());
        }
        let rsp: Q = protobuf::parse_from_bytes(&rsp.get_rsp_msg().value)
            .expect("Failed to parse response protobuf message");
        return Ok(rsp);
    }
}
