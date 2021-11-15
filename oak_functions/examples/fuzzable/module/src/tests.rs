//
// Copyright 2021 The Project Oak Authors
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

use crate::proto::{
    instruction::InstructionVariant, Instruction, Instructions, Panic, WriteResponse,
};
use maplit::hashmap;
use oak_functions_abi::proto::{ServerPolicy, StatusCode};

use oak_functions_loader::{
    grpc::{create_and_start_grpc_server, create_wasm_handler},
    logger::Logger,
    lookup::LookupData,
    metrics::{BucketConfig, PrivateMetricsConfig, PrivateMetricsProxyFactory},
    server::BoxedExtensionFactory,
};
use prost::Message;
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
};

use test_utils::{get_config_info, make_request};

#[tokio::test]
async fn test_server() {
    let server_port = test_utils::free_port();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, server_port));

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");

    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), false)
            .expect("Couldn't read Wasm module");

    let logger = Logger::for_test();

    let lookup_data = Arc::new(LookupData::new_empty(None, logger.clone()));

    let policy = ServerPolicy {
        constant_response_size_bytes: 100,
        constant_processing_time_ms: 200,
    };
    let metrics_factory = create_metrics_factory();
    let tee_certificate = vec![];
    let wasm_handler = create_wasm_handler(
        &wasm_module_bytes,
        lookup_data,
        vec![metrics_factory],
        logger.clone(),
    )
    .expect("could not create wasm_handler");

    let server_background = test_utils::background(|term| async move {
        create_and_start_grpc_server(
            &address,
            wasm_handler,
            tee_certificate,
            policy.clone(),
            get_config_info(&wasm_module_bytes, policy, false, None),
            term,
            logger,
        )
        .await
    });

    {
        // Send a request with an empty instruction list.
        let request = Instructions {
            instructions: vec![],
        };
        let mut request_bytes = vec![];
        request
            .encode(&mut request_bytes)
            .expect("Couldn't encode empty instruction list");
        let response = make_request(server_port, &request_bytes).await.response;
        assert_eq!(StatusCode::Success as i32, response.status,);
        assert_eq!(b"Done fuzzing!", response.body().unwrap());
    }

    {
        // Send a request to simulate a panic.
        let request = Instructions {
            instructions: vec![Instruction {
                instruction_variant: Some(InstructionVariant::Panic(Panic {})),
            }],
        };
        let mut request_bytes = vec![];
        request
            .encode(&mut request_bytes)
            .expect("Couldn't encode a single panic instruction");
        let response = make_request(server_port, &request_bytes).await.response;
        assert_eq!(StatusCode::Success as i32, response.status);

        // Expect an empty response.
        assert_eq!(0, response.body().unwrap().len());
    }

    {
        // Send a request to simulate a write_response followed by a panic.
        let request = Instructions {
            instructions: vec![
                Instruction {
                    instruction_variant: Some(InstructionVariant::WriteResponse(WriteResponse {
                        response: br"Random response!".to_vec(),
                    })),
                },
                Instruction {
                    instruction_variant: Some(InstructionVariant::Panic(Panic {})),
                },
            ],
        };
        let mut request_bytes = vec![];
        request
            .encode(&mut request_bytes)
            .expect("Couldn't encode instruction list");
        let response = make_request(server_port, &request_bytes).await.response;
        assert_eq!(StatusCode::Success as i32, response.status);

        // Expect non-empty response.
        assert_eq!(b"Random response!", response.body().unwrap());
    }

    let res = server_background.terminate_and_join().await;
    assert!(res.is_ok());
}

/// This is a slow test, intended for measuring and reporting the execution time of different types
/// of instructions. Run manually.
#[tokio::test]
#[ignore]
async fn large_wasm_invoke_test() {
    use oak_functions_abi::proto::Request;
    use oak_functions_loader::server::WasmHandler;
    use rand::{distributions::Alphanumeric, thread_rng, Rng};

    let logger = Logger::new(log::LevelFilter::Info);
    let entries = hashmap! {
        b"key_0".to_vec() => br#"value_0"#.to_vec(),
    };
    let lookup_data = Arc::new(LookupData::for_test(entries));
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
            .expect("Couldn't read Wasm module");

    let metrics_factory = create_metrics_factory();
    let wasm_handler = WasmHandler::create(
        &wasm_module_bytes,
        lookup_data,
        vec![metrics_factory],
        logger,
    )
    .expect("Couldn't create the server");

    let response: Vec<u8> = thread_rng()
        .sample_iter(&Alphanumeric)
        .take(256)
        .map(char::from)
        .collect::<String>()
        .into_bytes();
    let message = response.clone();

    let variants = vec![
        InstructionVariant::Panic(crate::proto::Panic {}),
        InstructionVariant::ReadRequest(crate::proto::ReadRequest {}),
        InstructionVariant::WriteResponse(crate::proto::WriteResponse { response }),
        InstructionVariant::WriteLogMessage(crate::proto::WriteLogMessage { message }),
        InstructionVariant::StorageGetItem(crate::proto::StorageGetItem {
            key: b"key".to_vec(),
        }),
        InstructionVariant::ReportEvent(crate::proto::ReportEvent {
            label: b"label".to_vec(),
        }),
    ];

    for variant in variants {
        let mut instructions = vec![];

        for _i in 0..50_000 {
            let inst = crate::proto::Instruction {
                instruction_variant: Some(variant.clone()),
            };
            instructions.push(inst);
        }
        let instructions = Instructions { instructions };

        let mut request_bytes = vec![];
        instructions
            .encode(&mut request_bytes)
            .expect("Couldn't encode instructions");

        let request = Request {
            body: request_bytes.clone(),
        };
        let now = std::time::Instant::now();
        let response = wasm_handler.clone().handle_invoke(request).await.unwrap();
        // The purpose of this test is to report some measurements about the execution time for each
        // type of instruction.
        println!(
            "variant: {:?}, elapsed time: {:.0?}",
            variant,
            now.elapsed().as_secs()
        );
        assert_eq!(StatusCode::Success as i32, response.status);
    }

    for count in vec![10_000, 20_000, 30_000, 40_000, 50_000] {
        let mut instructions = vec![];
        for _i in 0..count {
            let inst = crate::proto::Instruction {
                instruction_variant: Some(InstructionVariant::ReadRequest(
                    crate::proto::ReadRequest {},
                )),
            };
            instructions.push(inst);
        }
        let instructions = Instructions { instructions };

        let mut request_bytes = vec![];
        instructions
            .encode(&mut request_bytes)
            .expect("Couldn't encode instructions");

        let request = Request {
            body: request_bytes.clone(),
        };
        let now = std::time::Instant::now();
        let response = wasm_handler.clone().handle_invoke(request).await.unwrap();
        // Report the execution time measurements.
        println!(
            "count: {:?}, elapsed time: {:.0?}",
            count,
            now.elapsed().as_secs()
        );
        assert_eq!(StatusCode::Success as i32, response.status);
    }
}

fn create_metrics_factory() -> BoxedExtensionFactory {
    let metrics_config = PrivateMetricsConfig {
        epsilon: 1.0,
        batch_size: 20,
        buckets: hashmap! {"count".to_string() => BucketConfig::Count },
    };

    let metrics_factory =
        PrivateMetricsProxyFactory::new(&metrics_config, Logger::new(log::LevelFilter::Info))
            .expect("could not create PrivateMetricsProxyFactory");
    Box::new(metrics_factory)
}
