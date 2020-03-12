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
use std::collections::HashMap;
use std::process::Command;

// TODO(#544): re-enable unit tests of SDK functionality

/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(cargo_path: &str, module_name: &str) -> std::io::Result<Vec<u8>> {
    let mut cmd = cargo_metadata::MetadataCommand::new();
    cmd.manifest_path(cargo_path);
    let metadata = cmd.exec().unwrap();

    Command::new("cargo")
        .args(&[
            "build",
            "--target=wasm32-unknown-unknown",
            &format!("--manifest-path={}", cargo_path),
        ])
        .spawn()?
        .wait()?;

    let mut path = metadata.target_directory;
    path.push("wasm32-unknown-unknown/debug");
    path.push(module_name);

    std::fs::read(path)
}

const DEFAULT_LOG_CONFIG_NAME: &str = "log";
const DEFAULT_ENTRYPOINT_NAME: &str = "oak_main";
const DEFAULT_MODULE_MANIFEST: &str = "Cargo.toml";
const MODULE_WASM_SUFFIX: &str = ".wasm";

/// Convenience helper to build and run a single-Node Application with the
/// given module name, using the default name "oak_main" for its entrypoint.
pub fn run_single_module_default(
    module_config_name: &str,
) -> Result<(oak_runtime::RuntimeRef, oak_runtime::ChannelWriter), oak::OakStatus> {
    run_single_module(module_config_name, DEFAULT_ENTRYPOINT_NAME)
}

/// Convenience helper to build and run a single-Node application with the
/// given module name, using the provided entrypoint name.
pub fn run_single_module(
    module_config_name: &str,
    entrypoint_name: &str,
) -> Result<(oak_runtime::RuntimeRef, oak_runtime::ChannelWriter), oak::OakStatus> {
    let wasm: HashMap<String, Vec<u8>> = [(
        module_config_name.to_owned(),
        compile_rust_wasm(
            DEFAULT_MODULE_MANIFEST,
            &(module_config_name.to_owned() + MODULE_WASM_SUFFIX),
        )
        .expect("failed to build wasm module"),
    )]
    .iter()
    .cloned()
    .collect();

    let configuration = oak_runtime::application_configuration(
        wasm,
        DEFAULT_LOG_CONFIG_NAME,
        module_config_name,
        entrypoint_name,
    );

    oak_runtime::configure_and_run(configuration)
}

// TODO(#543): move this to oak_runtime as it's not test-specific
pub fn grpc_request<R, Q>(
    runtime: &oak_runtime::RuntimeRef,
    channel: &oak_runtime::ChannelWriter,
    method_name: &str,
    req: R,
) -> oak::grpc::Result<Q>
where
    R: protobuf::Message,
    Q: protobuf::Message,
{
    // Put the request in a GrpcRequest wrapper and serialize into a message.
    let grpc_req =
        oak::grpc::encap_request(req, None, method_name).expect("failed to build GrpcRequest");
    let mut req_msg = oak_runtime::Message {
        data: vec![],
        channels: vec![],
    };

    grpc_req
        .write_to_writer(&mut req_msg.data)
        .expect("failed to serialize GrpcRequest message");

    // Create a new channel to hold the request message.
    let (req_write_half, req_read_half) = runtime.new_channel();
    runtime
        .channel_write(&req_write_half, req_msg)
        .expect("could not write message");

    // Create a new channel for responses to arrive on and also attach that to the message.
    let (rsp_write_half, rsp_read_half) = runtime.new_channel();

    // Create a notification message and attach the method-invocation specific channels to it.
    let notify_msg = oak_runtime::Message {
        data: vec![],
        channels: vec![
            ChannelEither::Reader(req_read_half),
            ChannelEither::Writer(rsp_write_half),
        ],
    };

    // Send the notification message (with attached handles) into the Node under test.
    runtime
        .channel_write(channel, notify_msg)
        .expect("could not write message");

    // Read the serialized, encapsulated response.
    loop {
        let rsp = match runtime.channel_read(&rsp_read_half) {
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
