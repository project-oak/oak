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

use log::{debug, info};

use prost::Message;
use std::{collections::HashMap, process::Command};

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
        .env_remove("RUSTFLAGS")
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
) -> Result<(oak_runtime::RuntimeProxy, oak_abi::Handle), oak::OakStatus> {
    run_single_module(module_config_name, DEFAULT_ENTRYPOINT_NAME)
}

/// Convenience helper to build and run a single-Node application with the
/// given module name, using the provided entrypoint name.
pub fn run_single_module(
    module_config_name: &str,
    entrypoint_name: &str,
) -> Result<(oak_runtime::RuntimeProxy, oak_abi::Handle), oak::OakStatus> {
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

    oak_runtime::configure_and_run(configuration, oak_runtime::RuntimeConfiguration::default())
}

// TODO(#543): move this to oak_runtime as it's not test-specific
pub fn grpc_request<R, Q>(
    proxy: &oak_runtime::runtime::RuntimeProxy,
    handle: oak_abi::Handle,
    method_name: &str,
    req: &R,
) -> oak::grpc::Result<Q>
where
    R: prost::Message,
    Q: prost::Message + Default,
{
    // Put the request in a GrpcRequest wrapper and serialize into a message.
    let grpc_req =
        oak_abi::grpc::encap_request(req, method_name).expect("failed to build GrpcRequest");
    let mut req_msg = oak_runtime::NodeMessage {
        data: vec![],
        handles: vec![],
    };

    grpc_req
        .encode(&mut req_msg.data)
        .expect("failed to serialize GrpcRequest message");

    // Create a new channel to hold the request message.
    //
    // In most cases we do not care about labels, so we use the least privileged label for this
    // channel.
    let (req_write_handle, req_read_handle) =
        proxy.channel_create(&oak_abi::label::Label::public_trusted());
    proxy
        .channel_write(req_write_handle, req_msg)
        .expect("could not write message");

    // Create a new channel for responses to arrive on and also attach that to the message.
    //
    // In most cases we do not care about labels, so we use the least privileged label for this
    // channel.
    let (rsp_write_handle, rsp_read_handle) =
        proxy.channel_create(&oak_abi::label::Label::public_trusted());

    // Create a notification message and attach the method-invocation specific channels to it.
    let notify_msg = oak_runtime::NodeMessage {
        data: vec![],
        handles: vec![req_read_handle, rsp_write_handle],
    };

    // Send the notification message (with attached handles) into the Node under test.
    proxy
        .channel_write(handle, notify_msg)
        .expect("could not write message");
    proxy
        .channel_close(req_write_handle)
        .expect("failed to close channel");
    proxy
        .channel_close(req_read_handle)
        .expect("failed to close channel");
    proxy
        .channel_close(rsp_write_handle)
        .expect("failed to close channel");

    // Read the serialized, encapsulated response.
    loop {
        let rsp = match proxy.channel_read(rsp_read_handle) {
            Ok(Some(r)) => r,
            Ok(None) => {
                debug!("no pending gRPC response message; poll again soon");
                std::thread::sleep(std::time::Duration::from_millis(100));
                continue;
            }
            Err(e) => {
                panic!("failed to read from response channel: {:?}", e);
            }
        };
        proxy
            .channel_close(rsp_read_handle)
            .expect("failed to close channel");
        if rsp.data.is_empty() {
            info!("no pending message; poll again soon");
            std::thread::sleep(std::time::Duration::from_millis(100));
            continue;
        }
        let rsp = oak_abi::proto::oak::encap::GrpcResponse::decode(rsp.data.as_slice())
            .expect("failed to parse GrpcResponse message");
        if !rsp.last {
            panic!("Expected single final response");
        }

        let status = rsp.status.unwrap_or_default();
        if status.code != oak::grpc::Code::Ok as i32 {
            return Err(status);
        }
        let rsp =
            Q::decode(rsp.rsp_msg.as_slice()).expect("Failed to parse response protobuf message");
        return Ok(rsp);
    }
}
