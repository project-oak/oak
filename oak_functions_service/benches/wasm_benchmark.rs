//
// Copyright 2024 The Project Oak Authors
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

#![feature(never_type)]
#![feature(unwrap_infallible)]
#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

mod perf;

use std::sync::Arc;

use criterion::{BenchmarkId, Criterion, Throughput};
use criterion_macro::criterion;
use hashbrown::HashMap;
use oak_functions_abi::Request;
use oak_functions_service::{
    Handler,
    logger::StandaloneLogger,
    lookup::LookupDataManager,
    wasm::{WasmHandler, wasmtime::WasmtimeHandler},
};
use oak_micro_rpc::oak::functions::testing::TestModuleClient;
use oak_proto_rust::oak::functions::testing::{
    LookupRequest, LookupResponse, lookup_request::Mode,
};

const TEST_MODULE_PATH: &str = "oak_functions_test_module/oak_functions_test_module.wasm";
const ECHO_MODULE_PATH: &str = "oak_functions/examples/echo/echo.wasm";
const KEY_VALUE_LOOKUP_MODULE_PATH: &str =
    "oak_functions/examples/key_value_lookup/key_value_lookup.wasm";
#[criterion]
fn bench_invoke_echo(c: &mut Criterion) {
    let test_state = create_test_state_with_wasm_module_name::<WasmHandler>(ECHO_MODULE_PATH);

    // Measure throughput for different data sizes.
    let mut group = c.benchmark_group("echo wasm");
    for size in [0, 1, 10, 100, 1000].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let data = vec![88u8; size];
            b.iter(|| {
                let response =
                    test_state.wasm_handler.handle_invoke(Request { body: data.to_vec() }).unwrap();
                assert_eq!(response.body, data.to_vec());
            })
        });
    }
    group.finish();
}

#[criterion]
fn bench_invoke_lookup(c: &mut Criterion) {
    let test_state =
        create_test_state_with_wasm_module_name::<WasmHandler>(KEY_VALUE_LOOKUP_MODULE_PATH);

    const MAX_DATA_SIZE: i32 = 1000;
    const KEY_INDEX: i32 = 100;

    let test_data = create_test_data(0, MAX_DATA_SIZE);
    test_state
        .lookup_data_manager
        .extend_next_lookup_data(test_data.iter().map(|(k, v)| (k.as_ref(), v.as_ref())));
    test_state.lookup_data_manager.finish_next_lookup_data();

    c.bench_function("lookup wasm", |b| {
        let request = format!("key{KEY_INDEX}").into_bytes();
        let expected_response = format!("value{KEY_INDEX}").into_bytes();
        b.iter(|| {
            let response =
                test_state.wasm_handler.handle_invoke(Request { body: request.to_vec() }).unwrap();
            assert_eq!(response.body, expected_response);
        })
    });

    // Baseline for comparison.
    c.bench_function("lookup native", |b| {
        let request = format!("key{KEY_INDEX}").into_bytes();
        let expected_response = format!("value{KEY_INDEX}").into_bytes();
        b.iter(|| {
            let response = test_data.get(&request).unwrap();
            assert_eq!(response.as_ref(), expected_response);
        })
    });
}

struct Transport<'a, H: Handler> {
    wasm_handler: &'a mut H,
}

impl<H: Handler> micro_rpc::Transport for Transport<'_, H> {
    fn invoke(&mut self, request: &[u8]) -> Result<Vec<u8>, !> {
        Ok(self.wasm_handler.handle_invoke(Request { body: request.to_vec() }).unwrap().body)
    }
}

#[criterion]
fn bench_invoke_lookup_multi(c: &mut Criterion) {
    let mut test_state_wasmi =
        create_test_state_with_wasm_module_name::<WasmHandler>(TEST_MODULE_PATH);
    let mut test_state_wasmtime =
        create_test_state_with_wasm_module_name::<WasmtimeHandler>(TEST_MODULE_PATH);

    const MAX_DATA_SIZE: i32 = 1_000_000;
    const START_KEY_INDEX: i32 = 100;

    let test_data = create_test_data(0, MAX_DATA_SIZE);
    test_state_wasmi
        .lookup_data_manager
        .extend_next_lookup_data(test_data.iter().map(|(k, v)| (k.as_ref(), v.as_ref())));
    test_state_wasmi.lookup_data_manager.finish_next_lookup_data();

    test_state_wasmtime
        .lookup_data_manager
        .extend_next_lookup_data(test_data.iter().map(|(k, v)| (k.as_ref(), v.as_ref())));
    test_state_wasmtime.lookup_data_manager.finish_next_lookup_data();

    fn run_lookup_with_items<H: Handler>(
        b: &mut criterion::Bencher,
        test_state: &mut TestState<H>,
        items: i32,
        mode: Mode,
    ) {
        let lookup_request = LookupRequest {
            keys: (START_KEY_INDEX..START_KEY_INDEX + items)
                .map(|i| format!("key{}", i).into_bytes())
                .collect(),
            mode: mode.into(),
        };

        let expected_response = LookupResponse {
            values: (START_KEY_INDEX..START_KEY_INDEX + items)
                .map(|i| format!("value{}", i).into_bytes())
                .collect(),
        };

        let mut client =
            TestModuleClient::new(Transport { wasm_handler: &mut test_state.wasm_handler });

        b.iter(|| {
            let response = client.lookup(&lookup_request).into_ok().unwrap();
            assert_eq!(response, expected_response);
        })
    }

    let mut group = c.benchmark_group("lookup_multi wasm");
    for i in [1, 1000, 2000, 3000, 4000].iter() {
        group.bench_with_input(BenchmarkId::new("wasmtime batch", i), i, |b, &i| {
            run_lookup_with_items(b, &mut test_state_wasmtime, i, Mode::Batch);
        });
        group.bench_with_input(BenchmarkId::new("wasmtime individual", i), i, |b, &i| {
            run_lookup_with_items(b, &mut test_state_wasmtime, i, Mode::Individual);
        });
        group.bench_with_input(BenchmarkId::new("wasmi batch", i), i, |b, &i| {
            run_lookup_with_items(b, &mut test_state_wasmi, i, Mode::Batch);
        });
        group.bench_with_input(BenchmarkId::new("wasmi individual", i), i, |b, &i| {
            run_lookup_with_items(b, &mut test_state_wasmi, i, Mode::Individual);
        });
    }
    group.finish();
}

#[criterion(perf::flamegraph())]
fn flamegraph(c: &mut Criterion) {
    let mut test_state =
        create_test_state_with_wasm_module_name::<WasmtimeHandler>(TEST_MODULE_PATH);

    const MAX_DATA_SIZE: i32 = 1_000_000;
    const START_KEY_INDEX: i32 = 100;

    let test_data = create_test_data(0, MAX_DATA_SIZE);
    test_state
        .lookup_data_manager
        .extend_next_lookup_data(test_data.iter().map(|(k, v)| (k.as_ref(), v.as_ref())));
    test_state.lookup_data_manager.finish_next_lookup_data();

    fn run_lookup_with_items<H: Handler>(
        b: &mut criterion::Bencher,
        test_state: &mut TestState<H>,
        items: i32,
        mode: Mode,
    ) {
        let lookup_request = LookupRequest {
            keys: (START_KEY_INDEX..START_KEY_INDEX + items)
                .map(|i| format!("key{}", i).into_bytes())
                .collect(),
            mode: mode.into(),
        };

        let expected_response = LookupResponse {
            values: (START_KEY_INDEX..START_KEY_INDEX + items)
                .map(|i| format!("value{}", i).into_bytes())
                .collect(),
        };

        let mut client =
            TestModuleClient::new(Transport { wasm_handler: &mut test_state.wasm_handler });

        b.iter(|| {
            let response = client.lookup(&lookup_request).into_ok().unwrap();
            assert_eq!(response, expected_response);
        })
    }
    c.bench_function("flamegraph", |b| {
        run_lookup_with_items(b, &mut test_state, 1000, Mode::Individual)
    });
}

fn create_test_data(start: i32, end: i32) -> HashMap<Vec<u8>, Vec<u8>> {
    HashMap::from_iter(
        (start..end)
            .map(|i| (format!("key{}", i).into_bytes(), format!("value{}", i).into_bytes())),
    )
}

struct TestState<H: Handler> {
    wasm_handler: H::HandlerType,
    lookup_data_manager: Arc<LookupDataManager<16>>,
}

fn create_test_state_with_wasm_module_name<H: Handler>(wasm_module_path: &str) -> TestState<H> {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(Vec::new(), logger.clone()));
    let wasm_module_path = oak_file_utils::data_path(wasm_module_path);
    let wasm_module_bytes = std::fs::read(wasm_module_path).unwrap();

    let wasm_handler = H::new_handler(
        H::HandlerConfig::default(),
        &wasm_module_bytes,
        lookup_data_manager.clone(),
        None,
    )
    .unwrap();

    TestState { wasm_handler, lookup_data_manager }
}
