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
use oak_client::interceptors::{
    self, auth::AuthInterceptor, label::LabelInterceptor, CombinedInterceptor,
};
use std::{collections::HashMap, process::Command, sync::Arc};
use tonic::transport::{Certificate, Channel, ClientTlsConfig, Identity};

pub enum Profile {
    Release,
    Debug,
}

// TODO(#544): re-enable unit tests of SDK functionality

/// Returns the path to the Wasm file produced by compiling the provided `Cargo.toml` file.
fn build_wasm_module_path(metadata: &cargo_metadata::Metadata) -> String {
    let package_name = &metadata.root_package().unwrap().name;
    // Keep this in sync with `/runner/src/main.rs`.
    format!("{}/bin/{}.wasm", metadata.workspace_root, package_name)
}

/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(manifest_path: &str, profile: Profile) -> anyhow::Result<Vec<u8>> {
    let metadata = cargo_metadata::MetadataCommand::new()
        .manifest_path(manifest_path)
        .exec()
        .unwrap();
    // Keep this in sync with `/oak_functions/sdk/test/utils/src/lib.rs`.
    // Keep this in sync with `/runner/src/main.rs`.
    let mut args = vec![
        // `--out-dir` is unstable and requires `-Zunstable-options`.
        "-Zunstable-options".to_string(),
        "build".to_string(),
        "--target=wasm32-unknown-unknown".to_string(),
        format!("--target-dir={}/wasm", metadata.target_directory),
        format!("--out-dir={}/bin", metadata.workspace_root),
        format!("--manifest-path={}", manifest_path),
    ];
    match profile {
        Profile::Release => {
            args.push("--release".to_string());
        }
        Profile::Debug => {}
    };

    Command::new("cargo")
        .args(args)
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("Couldn't spawn cargo build")?
        .wait()
        .context("Couldn't wait for cargo build to finish")?;

    let module_path = build_wasm_module_path(&metadata);
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

/// Convenience helper to build and run a single-Node Application using the default name "oak_main"
/// for its entrypoint.
pub fn run_single_module_default(
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakError> {
    run_single_module(DEFAULT_ENTRYPOINT_NAME, permissions)
}

/// Convenience helper to build and run a single-Node application with the provided entrypoint name.
pub fn run_single_module(
    entrypoint_name: &str,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakError> {
    run_single_module_with_config(entrypoint_name, ConfigMap::default(), permissions)
}

/// Convenience helper to build and run a single-Node application with the provided entrypoint name,
/// passing in the provided `ConfigMap` at start-of-day.
pub fn run_single_module_with_config(
    entrypoint_name: &str,
    config_map: ConfigMap,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> Result<Arc<oak_runtime::Runtime>, oak::OakError> {
    let combined_config = runtime_config(entrypoint_name, config_map, permissions);
    oak_runtime::configure_and_run(combined_config)
}

/// Build the configuration needed to launch a test Runtime instance that runs a single-Node
/// application with the provided entrypoint name.
///
/// The Wasm module is compiled with [`Profile::Release`] in order to maintain its SHA256 hash
/// consistent.
pub fn runtime_config(
    entrypoint_name: &str,
    config_map: ConfigMap,
    permissions: oak_runtime::permissions::PermissionsConfiguration,
) -> oak_runtime::RuntimeConfiguration {
    let wasm: HashMap<String, Vec<u8>> = [(
        DEFAULT_MODULE_NAME.to_string(),
        compile_rust_wasm(DEFAULT_MODULE_MANIFEST, Profile::Release)
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
pub async fn public_channel_and_interceptor() -> (Channel, LabelInterceptor) {
    channel_and_interceptor(&Label::public_untrusted()).await
}

/// Build a channel and a label interceptor suitable for building a client that connects to a
/// Runtime under test. The interceptor uses the given key pair to attach a signature and public-key
/// identity tag to every request.
pub async fn private_channel_and_interceptor(
    key_pair: oak_sign::KeyPair,
) -> (
    Channel,
    CombinedInterceptor<LabelInterceptor, AuthInterceptor>,
) {
    let (channel, label_interceptor) = channel_and_interceptor(&confidentiality_label(
        public_key_identity_tag(&key_pair.public_key_der().unwrap()),
    ))
    .await;
    let auth_interceptor = AuthInterceptor::create(key_pair);
    let interceptor = interceptors::combine(label_interceptor, auth_interceptor);

    (channel, interceptor)
}
