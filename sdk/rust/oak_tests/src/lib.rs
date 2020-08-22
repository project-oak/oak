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

use anyhow::Context;
use log::{debug, info};
use oak_abi::{
    label::Label,
    proto::oak::application::{
        node_configuration::ConfigType, ApplicationConfiguration, ConfigMap, NodeConfiguration,
        WebAssemblyConfiguration,
    },
};
use prost::Message;
use std::{collections::HashMap, path::PathBuf, process::Command, sync::Arc};
use tonic::{
    metadata::MetadataValue,
    transport::{Certificate, Channel, ClientTlsConfig, Identity},
    Request,
};

// TODO(#544): re-enable unit tests of SDK functionality

/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(cargo_path: &str, module_wasm_file_name: &str) -> anyhow::Result<Vec<u8>> {
    // Use a separate target dir for Wasm build artifacts. The precise name is not relevant, but it
    // should end with `target` so that it gets automatically ignored by our `.gitignore`.
    let target_dir = PathBuf::from("oak_tests/target");

    Command::new("cargo")
        .args(&[
            "build",
            &format!(
                "--target-dir={}",
                target_dir.to_str().expect("invalid target dir")
            ),
            "--target=wasm32-unknown-unknown",
            &format!("--manifest-path={}", cargo_path),
        ])
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("could not spawn cargo build")?
        .wait()
        .context("could not wait for cargo build to finish")?;

    let mut module_path = target_dir;
    module_path.push("wasm32-unknown-unknown/debug");
    module_path.push(module_wasm_file_name);

    info!("compiled Wasm module path: {:?}", module_path);

    std::fs::read(module_path).context("could not read compiled module")
}

/// Default module name for the module under test.
const DEFAULT_MODULE_NAME: &str = "app";
/// Default entrypoint name for the module under test.
const DEFAULT_ENTRYPOINT_NAME: &str = "oak_main";
/// Default URI that the tests expect to find a live Runtime at.
const RUNTIME_URI: &str = "https://localhost:8080";

const DEFAULT_MODULE_MANIFEST: &str = "Cargo.toml";

// Retry parameters when connecting to a gRPC server.
const RETRY_COUNT: u32 = 360;
const RETRY_INTERVAL: std::time::Duration = std::time::Duration::from_millis(500);

/// Convenience helper to build and run a single-Node Application with the given module name, using
/// the default name "oak_main" for its entrypoint.
pub fn run_single_module_default(
    module_config_name: &str,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakStatus> {
    run_single_module(module_config_name, DEFAULT_ENTRYPOINT_NAME)
}

/// Convenience helper to build and run a single-Node application with the given Wasm module file
/// name, using the provided entrypoint name.
pub fn run_single_module(
    module_wasm_file_name: &str,
    entrypoint_name: &str,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakStatus> {
    run_single_module_with_config(module_wasm_file_name, entrypoint_name, ConfigMap::default())
}

/// Convenience helper to build and run a single-Node application with the given Wasm module file
/// name, using the provided entrypoint name, passing in the provided `ConfigMap` at start-of-day.
pub fn run_single_module_with_config(
    module_wasm_file_name: &str,
    entrypoint_name: &str,
    config_map: ConfigMap,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakStatus> {
    let combined_config = runtime_config(module_wasm_file_name, entrypoint_name, config_map);
    oak_runtime::configure_and_run(combined_config)
}

/// Build the configuration needed to launch a test Runtime instance that runs a single-Node
/// application with the given Wasm module file name and entrypoint.
pub fn runtime_config(
    module_wasm_file_name: &str,
    entrypoint_name: &str,
    config_map: ConfigMap,
) -> oak_runtime::RuntimeConfiguration {
    let wasm: HashMap<String, Vec<u8>> = [(
        DEFAULT_MODULE_NAME.to_string(),
        compile_rust_wasm(DEFAULT_MODULE_MANIFEST, module_wasm_file_name)
            .expect("failed to build wasm module"),
    )]
    .iter()
    .cloned()
    .collect();

    runtime_config_wasm(wasm, DEFAULT_MODULE_NAME, entrypoint_name, config_map)
}

/// Build the configuration needed to launch a test Runtime instance that runs the given collection
/// of Wasm modules, starting with the given module name and entrypoint.
pub fn runtime_config_wasm(
    wasm_modules: HashMap<String, Vec<u8>>,
    module_config_name: &str,
    entrypoint_name: &str,
    config_map: ConfigMap,
) -> oak_runtime::RuntimeConfiguration {
    oak_runtime::RuntimeConfiguration {
        metrics_port: Some(9090),
        introspect_port: Some(1909),
        grpc_config: oak_runtime::GrpcConfiguration {
            grpc_server_tls_identity: Some(Identity::from_pem(
                include_str!("../certs/local.pem"),
                include_str!("../certs/local.key"),
            )),
            grpc_client_root_tls_certificate: Some(
                oak_runtime::config::load_certificate(&include_str!("../certs/ca.pem")).unwrap(),
            ),
            oidc_client_info: None,
        },
        app_config: ApplicationConfiguration {
            wasm_modules,
            initial_node_configuration: Some(NodeConfiguration {
                name: "test".to_string(),
                config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                    wasm_module_name: module_config_name.to_string(),
                    wasm_entrypoint_name: entrypoint_name.to_string(),
                })),
            }),
        },
        config_map,
        sign_table: oak_runtime::SignatureTable::default(),
    }
}

/// Build a channel and interceptor suitable for building a client that connects
/// to a Runtime under test.
pub async fn channel_and_interceptor() -> (Channel, impl Into<tonic::Interceptor>) {
    // Build a channel that connects to the Runtime under test.
    let uri = RUNTIME_URI.parse().expect("Error parsing URI");
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(Certificate::from_pem(include_str!("../certs/ca.pem")));
    let builder = Channel::builder(uri)
        .tls_config(tls_config)
        .expect("Couldn't create TLS configuration");

    // The Runtime may have just been started for a test, and make take some time
    // to come fully up, start a gRPC server and accept connections. Allow for
    // this by retrying at intervals until the server responds or we hit a retry
    // limit.
    let mut retries = 0;
    let channel;
    loop {
        match builder.connect().await {
            Ok(c) => {
                debug!("Connected to gRPC server");
                channel = c;
                break;
            }
            Err(err) => {
                if retries < RETRY_COUNT {
                    debug!("Failed to connect, try again momentarily: {:?}", err);
                    retries += 1;
                    std::thread::sleep(RETRY_INTERVAL);
                } else {
                    panic!("Failed to connect, last err: {:?}", err);
                }
            }
        }
    }

    // Build an interceptor that will attach a public-untrusted Oak label to
    // every gRPC request.
    let mut label = Vec::new();
    Label::public_untrusted()
        .encode(&mut label)
        .expect("Error encoding label");
    let interceptor = move |mut request: Request<()>| {
        request.metadata_mut().insert_bin(
            oak_abi::OAK_LABEL_GRPC_METADATA_KEY,
            MetadataValue::from_bytes(label.as_ref()),
        );
        Ok(request)
    };

    (channel, interceptor)
}
