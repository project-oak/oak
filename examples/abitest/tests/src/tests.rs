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

use abitest_grpc::proto::{oak_abi_test_service_client::OakAbiTestServiceClient, AbiTestRequest};
use assert_matches::assert_matches;
use log::{error, info};
use maplit::hashmap;
use std::collections::HashMap;

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

#[tokio::test(core_threads = 2)]
async fn test_abi() {
    env_logger::init();

    let wasm_modules = build_wasm().expect("failed to build wasm modules");
    let config = oak_tests::runtime_config_wasm(
        wasm_modules,
        FRONTEND_MODULE_NAME,
        FRONTEND_ENTRYPOINT_NAME,
        None,
    );
    let runtime =
        oak_runtime::configure_and_run(config).expect("unable to configure runtime with test wasm");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = OakAbiTestServiceClient::with_interceptor(channel, interceptor);

    // Skip tests that require the existence of an external service.
    let mut req = AbiTestRequest::default();
    req.exclude = "(Storage|GrpcClient|Roughtime)".to_string();

    info!("Sending request: {:?}", req);
    let result = client.run_tests(req).await;
    assert_matches!(result, Ok(_));

    info!("Runtime graph at exit is:\n{}", runtime.graph());

    runtime.stop();

    let mut disabled = 0;
    let mut success = true;
    let results = result.unwrap().into_inner().results;
    for result in results {
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
