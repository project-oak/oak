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
    label::{confidentiality_label, public_key_identity_tag, Label},
    proto::oak::application::{
        node_configuration::ConfigType, ApplicationConfiguration, ConfigMap, NodeConfiguration,
        WebAssemblyConfiguration,
    },
};
use oak_client::interceptors::label::LabelInterceptor;
use std::{collections::HashMap, path::PathBuf, process::Command, sync::Arc};
use tonic::transport::{Certificate, Channel, ClientTlsConfig, Identity};

pub enum Profile {
    Release,
    Debug,
}

// TODO(#544): re-enable unit tests of SDK functionality

/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(
    manifest_path: &str,
    module_wasm_file_name: &str,
    profile: Profile,
) -> anyhow::Result<Vec<u8>> {
    // Use a fixed target directory, because `--target-dir` influences SHA256 hash of Wasm module.
    // Directory should end with `target` so that it gets automatically ignored by our `.gitignore`.
    let mut target_dir = PathBuf::from(manifest_path);
    target_dir.pop();
    target_dir.push("target");

    let mut args = vec![
        "build".to_string(),
        format!(
            "--target-dir={}",
            target_dir.to_str().expect("Invalid target dir")
        ),
        "--target=wasm32-unknown-unknown".to_string(),
        format!("--manifest-path={}", manifest_path),
    ];
    let profile_str = match profile {
        Profile::Release => {
            args.push("--release".to_string());
            "release".to_string()
        }
        Profile::Debug => "debug".to_string(),
    };

    Command::new("cargo")
        .args(args)
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("Couldn't spawn cargo build")?
        .wait()
        .context("Couldn't wait for cargo build to finish")?;

    let mut module_path = target_dir;
    module_path.push(format!("wasm32-unknown-unknown/{}", profile_str));
    module_path.push(module_wasm_file_name);

    info!("Compiled Wasm module path: {:?}", module_path);

    std::fs::read(module_path).context("Couldn't read compiled module")
}

/// Default module name for the module under test.
const DEFAULT_MODULE_NAME: &str = "app";
/// Default entrypoint name for the module under test.
const DEFAULT_ENTRYPOINT_NAME: &str = "oak_main";
/// Default URI that the tests expect to find a live Runtime at.
const RUNTIME_URI: &str = "https://localhost:8080";

const DEFAULT_MODULE_MANIFEST: &str = "Cargo.toml";

// Retry parameters when connecting to a gRPC server.
const RETRY_COUNT: u32 = 600;
const RETRY_INTERVAL: std::time::Duration = std::time::Duration::from_millis(800);

/// Convenience helper to build and run a single-Node Application with the given module name, using
/// the default name "oak_main" for its entrypoint.
pub fn run_single_module_default(
    module_config_name: &str,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakError> {
    run_single_module(module_config_name, DEFAULT_ENTRYPOINT_NAME, permissions)
}

/// Convenience helper to build and run a single-Node application with the given Wasm module file
/// name, using the provided entrypoint name.
pub fn run_single_module(
    module_wasm_file_name: &str,
    entrypoint_name: &str,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakError> {
    run_single_module_with_config(
        module_wasm_file_name,
        entrypoint_name,
        ConfigMap::default(),
        permissions,
    )
}

/// Convenience helper to build and run a single-Node application with the given Wasm module file
/// name, using the provided entrypoint name, passing in the provided `ConfigMap` at start-of-day.
pub fn run_single_module_with_config(
    module_wasm_file_name: &str,
    entrypoint_name: &str,
    config_map: ConfigMap,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakError> {
    let combined_config = runtime_config(
        module_wasm_file_name,
        entrypoint_name,
        config_map,
        permissions,
    );
    oak_runtime::configure_and_run(combined_config)
}

/// Build the configuration needed to launch a test Runtime instance that runs a single-Node
/// application with the given Wasm module file name and entrypoint.
/// Wasm module compiled with [`Profile::Release`] in order to keep its SHA256 hash.
pub fn runtime_config(
    module_wasm_file_name: &str,
    entrypoint_name: &str,
    config_map: ConfigMap,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> oak_runtime::RuntimeConfiguration {
    let wasm: HashMap<String, Vec<u8>> = [(
        DEFAULT_MODULE_NAME.to_string(),
        compile_rust_wasm(
            DEFAULT_MODULE_MANIFEST,
            module_wasm_file_name,
            Profile::Release,
        )
        .expect("failed to build wasm module"),
    )]
    .iter()
    .cloned()
    .collect();

    runtime_config_wasm(
        wasm,
        DEFAULT_MODULE_NAME,
        entrypoint_name,
        config_map,
        permissions,
        oak_runtime::SignatureTable::default(),
    )
}

/// Build the configuration needed to launch a test Runtime instance that runs the given collection
/// of Wasm modules, starting with the given module name and entrypoint.
pub fn runtime_config_wasm(
    wasm_modules: HashMap<String, Vec<u8>>,
    module_config_name: &str,
    entrypoint_name: &str,
    config_map: ConfigMap,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
    sign_table: oak_runtime::SignatureTable,
) -> oak_runtime::RuntimeConfiguration {
    oak_runtime::RuntimeConfiguration {
        metrics_port: Some(9090),
        introspect_port: Some(1909),
        kms_credentials: None,
        secure_server_configuration: oak_runtime::SecureServerConfiguration {
            grpc_config: Some(oak_runtime::GrpcConfiguration {
                grpc_server_tls_identity: Some(Identity::from_pem(
                    include_str!("../certs/local.pem"),
                    include_str!("../certs/local.key"),
                )),
                grpc_client_root_tls_certificate: oak_runtime::tls::Certificate::parse(
                    include_bytes!("../certs/ca.pem").to_vec(),
                )
                .ok(),
                oidc_client_info: None,
            }),
            http_config: create_http_config(),
        },
        app_config: ApplicationConfiguration {
            wasm_modules,
            initial_node_configuration: Some(NodeConfiguration {
                config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                    wasm_module_name: module_config_name.to_string(),
                    wasm_entrypoint_name: entrypoint_name.to_string(),
                })),
            }),
            module_signatures: vec![],
        },
        permissions_config: permissions,
        config_map,
        sign_table,
    }
}

/// Tries to create a [`oak_runtime::HttpConfiguration`]. Returns `None`, if any of the paths does
/// not represent a valid file.
fn create_http_config() -> Option<oak_runtime::HttpConfiguration> {
    let tls_config = oak_runtime::tls::TlsConfig::new(
        "../../../certs/local/local.pem",
        "../../../certs/local/local.key",
    )?;
    Some(oak_runtime::HttpConfiguration {
        tls_config,
        http_client_root_tls_certificate: oak_runtime::tls::Certificate::parse(
            include_bytes!("../certs/ca.pem").to_vec(),
        )
        .ok(),
    })
}

/// Build a labeled channel and interceptor suitable for building a client that
/// connects to a Runtime under test.
pub async fn channel_and_interceptor(label: &Label) -> (Channel, LabelInterceptor) {
    // Build a channel that connects to the Runtime under test.
    let uri = RUNTIME_URI.parse().expect("Error parsing URI");
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(Certificate::from_pem(include_str!("../certs/ca.pem")));
    let builder = Channel::builder(uri)
        .tls_config(tls_config)
        .expect("Couldn't create TLS configuration");

    // The Runtime may have just been started for a test, and may take some time
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

    // Build an interceptor that will attach the given Oak label to every gRPC request.
    let interceptor = LabelInterceptor::create(label).expect("Couldn't create label interceptor.");

    (channel, interceptor)
}

/// Build a public-untrusted channel and interceptor suitable for building a
/// client that connects to a Runtime under test.
pub async fn public_channel_and_interceptor() -> (Channel, impl Into<tonic::Interceptor>) {
    channel_and_interceptor(&Label::public_untrusted()).await
}

/// Build a channel and a label interceptor suitable for building a client that connects to a
/// Runtime under test. The interceptor uses the given public key to attach a public-key identity
/// tag to every request.
pub async fn authenticated_channel_and_interceptor(
    public_key: &[u8],
) -> (Channel, LabelInterceptor) {
    channel_and_interceptor(&confidentiality_label(public_key_identity_tag(public_key))).await
}
