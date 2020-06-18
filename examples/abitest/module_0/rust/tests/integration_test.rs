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
use log::{debug, error, info};
use maplit::hashmap;
use serial_test::serial;
use std::{
    collections::HashMap,
    sync::{Arc, Once},
};

// Constants for Node config names that should match those in the textproto
// config held in ../../../config.
const FRONTEND_MODULE_NAME: &str = "frontend_module";
const BACKEND_MODULE_NAME: &str = "backend_module";
const FRONTEND_ENTRYPOINT_NAME: &str = "frontend_oak_main";

const FRONTEND_MANIFEST: &str = "../../module_0/rust/Cargo.toml";
const BACKEND_MANIFEST: &str = "../../module_1/rust/Cargo.toml";

const FRONTEND_WASM_NAME: &str = "abitest_0_frontend.wasm";
const BACKEND_WASM_NAME: &str = "abitest_1_backend.wasm";

fn build_wasm() -> std::io::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        FRONTEND_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(FRONTEND_MANIFEST, FRONTEND_WASM_NAME)?,
        BACKEND_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(BACKEND_MANIFEST, BACKEND_WASM_NAME)?,
    })
}

static LOG_INIT_ONCE: Once = Once::new();

async fn setup() -> (
    Arc<oak_runtime::Runtime>,
    OakAbiTestServiceClient<tonic::transport::Channel>,
) {
    LOG_INIT_ONCE.call_once(|| {
        // Logger panics if it is initalized more than once.
        env_logger::init();
    });

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
    let client = OakAbiTestServiceClient::with_interceptor(channel, interceptor);

    (runtime, client)
}

#[tokio::test(core_threads = 2)]
#[serial]
async fn test_abi() {
    let (runtime, mut client) = setup().await;

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

#[tokio::test(core_threads = 2)]
#[serial]
async fn test_leaks() {
    let (runtime, mut client) = setup().await;

    let (before_nodes, before_channels) = runtime.object_counts();
    info!(
        "Counts before test: Nodes={}, Channels={}",
        before_nodes, before_channels
    );

    // Run tests that are supposed to leave Node/channel counts unchanged.
    let mut req = AbiTestRequest::default();
    req.include = "Idem".to_string();

    debug!("Sending request: {:?}", req);
    let result = client.run_tests(req).await;
    assert_matches!(result, Ok(_));
    let results = result.unwrap().into_inner().results;

    let (after_nodes, after_channels) = runtime.object_counts();
    info!(
        "Counts change from test: Nodes={} => {}, Channels={} => {}",
        before_nodes, after_nodes, before_channels, after_channels
    );

    if before_nodes != after_nodes || before_channels != after_channels {
        // One of the batch of tests has triggered a different object count.
        // Repeat the tests one by one to find out which.
        let mut details = Vec::new();
        for result in results {
            if result.disabled {
                continue;
            }

            let (before_nodes, before_channels) = runtime.object_counts();
            let mut req = AbiTestRequest::default();
            req.include = format!("^{}$", result.name);
            debug!("Sending request: {:?}", req);
            let this_result = client.run_tests(req).await;
            assert_matches!(this_result, Ok(_));
            let (after_nodes, after_channels) = runtime.object_counts();

            if (before_nodes != after_nodes) || (before_channels != after_channels) {
                details.push(format!(
                    "[ LEAK ] {} ({}=>{} nodes, {}=>{} channels)",
                    result.name, before_nodes, after_nodes, before_channels, after_channels,
                ));
            } else {
                details.push(format!("[  OK  ] {}", result.name,));
            }
        }
        for detail in details {
            info!("{}", detail);
        }
        panic!("Leak of Nodes or channels found");
    }

    runtime.stop();
}
