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

use abitest_0_frontend::proto::{AbiTestRequest, AbiTestResponse};
use assert_matches::assert_matches;
use log::{error, info};
use maplit::hashmap;
use oak::grpc;
use oak_abi::proto::oak::application::ApplicationConfiguration;
use std::collections::HashMap;
use tonic::transport::Certificate;

// Constants for Node config names that should match those in the textproto
// config held in ../../client/config.h.
const FRONTEND_MODULE_NAME: &str = "frontend_module";
const BACKEND_MODULE_NAME: &str = "backend_module";
const FRONTEND_ENTRYPOINT_NAME: &str = "frontend_oak_main";

const FRONTEND_MANIFEST: &str = "../module_0/rust/Cargo.toml";
const BACKEND_MANIFEST: &str = "../module_1/rust/Cargo.toml";

const FRONTEND_WASM_NAME: &str = "abitest_0_frontend.wasm";
const BACKEND_WASM_NAME: &str = "abitest_1_backend.wasm";

fn build_wasm() -> std::io::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        FRONTEND_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(FRONTEND_MANIFEST, FRONTEND_WASM_NAME)?,
        BACKEND_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(BACKEND_MANIFEST, BACKEND_WASM_NAME)?,
    })
}

#[test]
fn test_abi() {
    simple_logger::init_by_env();

    let application_configuration = ApplicationConfiguration {
        wasm_modules: build_wasm().expect("failed to build wasm modules"),
        initial_node_configuration: Some(oak::node_config::wasm(
            FRONTEND_MODULE_NAME,
            FRONTEND_ENTRYPOINT_NAME,
        )),
    };

    let (runtime, entry_channel) = oak_runtime::configure_and_run(
        application_configuration,
        oak_runtime::RuntimeConfiguration::default(),
        oak_runtime::GrpcConfiguration {
            grpc_server_tls_identity: None,
            oidc_client_info: None,
            // Some of the tests require a gRPC client, so we populate the required certificate with
            // an invalid value here, even though it will still fail when instantiating the actual
            // gRPC client.
            grpc_client_root_tls_certificate: Some(Certificate::from_pem("invalid-cert")),
        },
    )
    .expect("unable to configure runtime with test wasm");

    // TODO(#540): reinstate storage, gRPC client and Roughtime tests when Rust
    // runtime supports them.
    let mut req = AbiTestRequest::default();
    req.exclude = "(Storage|GrpcClient|Roughtime)".to_string();

    let result: grpc::Result<AbiTestResponse> = oak_tests::grpc_request(
        &runtime,
        entry_channel,
        "/oak.examples.abitest.OakABITestService/RunTests",
        &req,
    );
    assert_matches!(result, Ok(_));

    info!("Runtime graph at exit is:\n{}", runtime.graph_runtime());

    runtime.stop_runtime();

    let mut disabled = 0;
    let mut success = true;
    for result in result.unwrap().results {
        if result.disabled {
            disabled += 1;
            continue;
        }
        info!(
            "[ {} ] {}",
            if result.success { " OK " } else { "FAIL" },
            result.name
        );
        if !result.success {
            error!("Failure details: {}", result.details);
            success = false;
        }
    }
    if disabled > 0 {
        info!("YOU HAVE {} DISABLED TESTS", disabled);
    }
    assert_eq!(true, success);
}
