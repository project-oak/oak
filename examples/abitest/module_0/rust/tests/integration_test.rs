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
use anyhow::Context;
use assert_matches::assert_matches;
use log::{debug, error, info};
use maplit::hashmap;
use oak_abi::proto::oak::application::ConfigMap;
use oak_client::interceptors::label::LabelInterceptor;
use serial_test::serial;
use std::{collections::HashMap, sync::Arc};
use tokio::time::{sleep, Duration};
use tonic::{service::interceptor::InterceptedService, transport::Channel};

// Constants for Node config names that should match those in the textproto
// config held in ../../../config.
const FRONTEND_MODULE_NAME: &str = "frontend_module";
const BACKEND_MODULE_NAME: &str = "backend_module";
const LINEAR_HANDLES_MODULE_NAME: &str = "linear_handles_module";
const FRONTEND_ENTRYPOINT_NAME: &str = "frontend_oak_main";

const FRONTEND_MANIFEST: &str = "../../module_0/rust/Cargo.toml";
const BACKEND_MANIFEST: &str = "../../module_1/rust/Cargo.toml";
const LINEAR_HANDLES_MANIFEST: &str = "../../module_linear_handles/rust/Cargo.toml";

fn build_wasm() -> anyhow::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        FRONTEND_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(FRONTEND_MANIFEST, oak_tests::Profile::Debug).context("could not compile frontend module")?,
        BACKEND_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(BACKEND_MANIFEST, oak_tests::Profile::Debug).context("could not compile backend module")?,
        LINEAR_HANDLES_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(LINEAR_HANDLES_MANIFEST, oak_tests::Profile::Debug).context("could not compile linear_handles module")?,
    })
}

async fn setup() -> (
    Arc<oak_runtime::Runtime>,
    OakAbiTestServiceClient<InterceptedService<Channel, LabelInterceptor>>,
) {
    let _ = env_logger::builder().is_test(true).try_init();
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_http_server_nodes: true,
        allow_log_nodes: true,
        allow_insecure_http_egress: true,
        allow_egress_https_authorities: vec!["localhost:7856".to_string()],
    };

    let wasm_modules = build_wasm().expect("failed to build wasm modules");
    let config = oak_tests::runtime_config_wasm(
        wasm_modules,
        FRONTEND_MODULE_NAME,
        FRONTEND_ENTRYPOINT_NAME,
        ConfigMap::default(),
        permissions,
        oak_runtime::SignatureTable::default(),
    );
    let runtime =
        oak_runtime::configure_and_run(config).expect("unable to configure runtime with test wasm");

    let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
    let client = OakAbiTestServiceClient::with_interceptor(channel, interceptor);

    (runtime, client)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
#[serial]
async fn test_abi() {
    let (runtime, mut client) = setup().await;
    {
        // Skip tests that require the existence of an external service.
        //  - storage and gRPC client test require details of a gRPC service to connect to
        //  - Roughtime tests connect to the internet.
        let req = AbiTestRequest {
            exclude: "(Storage|GrpcClient|Roughtime)".to_string(),
            ..Default::default()
        };

        info!("Sending request: {:?}", req);
        let result = client.run_tests(req).await;
        assert_matches!(result, Ok(_));

        info!("Runtime graph at exit is:\n{}", runtime.graph());

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
        assert!(success);
    } // ensure futures are all dropped
    drop(client);
    runtime.stop();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
#[serial]
async fn test_leaks() {
    let (runtime, mut client) = setup().await;

    {
        let (before_nodes, before_channels) = runtime.object_counts();
        info!(
            "Counts before test: Nodes={}, Channels={}",
            before_nodes, before_channels
        );

        // Run tests that are supposed to leave Node/channel counts in a known state.
        // Skip tests that require the existence of an external service.
        //  - storage and gRPC client test require details of a gRPC service to connect to
        //  - Roughtime tests connect to the internet.
        let req = AbiTestRequest {
            exclude: "(Storage|GrpcClient|Roughtime)".to_string(),
            predictable_counts: true,
            ..Default::default()
        };

        debug!("Sending request: {:?}", req);
        let result = client.run_tests(req).await;
        assert_matches!(result, Ok(_));
        let results = result.unwrap().into_inner().results;

        // Calculate the expected change in Node and channel counts for
        // these tests.
        let mut want_nodes = before_nodes;
        let mut want_channels = before_channels;
        for result in &results {
            assert!(result.predictable_counts);
            if result.disabled {
                continue;
            }
            want_nodes += result.node_change;
            want_channels += result.channel_change;
        }

        let (after_nodes, after_channels) = runtime.object_counts();
        // If the values don't match the expected values it could be due to a race condition where a
        // backend node closed its orphaned channeal a bit later than expected, so we wait 5 seconds
        // and calculate the values again.
        let (after_nodes, after_channels) =
            if after_nodes != want_nodes || after_channels != want_channels {
                sleep(Duration::from_secs(5)).await;
                runtime.object_counts()
            } else {
                (after_nodes, after_channels)
            };

        info!(
            "Counts change from test: Nodes={} => {}, Channels={} => {}",
            before_nodes, after_nodes, before_channels, after_channels
        );

        if after_nodes != want_nodes || after_channels != want_channels {
            error!(
                "Batch test showed unexpected count change: got: node_delta={} channel_delta={}, want node_delta={} channel_delta={}",
                (after_nodes-before_nodes), (after_channels-before_channels),
                (want_nodes-before_nodes), (want_channels-before_channels),
            );
            // One of the batch of tests has triggered an unexpected object count.
            // Repeat the tests one by one to find out which.
            let mut details = Vec::new();
            for result in results {
                if result.disabled {
                    continue;
                }

                let (before_nodes, before_channels) = runtime.object_counts();
                let (want_nodes, want_channels) = (
                    before_nodes + result.node_change,
                    before_channels + result.channel_change,
                );

                let req = AbiTestRequest {
                    include: format!("^{}$", result.name),
                    ..Default::default()
                };
                debug!("Sending request: {:?}", req);
                let this_result = client.run_tests(req).await;
                assert_matches!(this_result, Ok(_));
                let (after_nodes, after_channels) = runtime.object_counts();

                if after_nodes != want_nodes || after_channels != want_channels {
                    details.push(format!(
                    "[ LEAK ] {} (got {}=>{} nodes, {}=>{} channels, want {}=>{} nodes, {}=>{} channels)",
                    result.name, before_nodes, after_nodes, before_channels, after_channels,
                    before_nodes, want_nodes, before_channels, want_channels,
                ));
                } else {
                    details.push(format!(
                        "[ OK ] {} ({}=>{} nodes, {}=>{} channels, as expected)",
                        result.name, before_nodes, after_nodes, before_channels, after_channels,
                    ));
                }
            }
            for detail in details {
                info!("{}", detail);
            }
            panic!("Leak of Nodes or channels found");
        }
    } // ensure futures are all dropped
    drop(client);
    runtime.stop();
}
