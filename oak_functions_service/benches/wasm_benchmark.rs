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

use std::sync::Arc;

use bytes::Bytes;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hashbrown::HashMap;
use oak_functions_abi::Request;
use oak_functions_service::{
    logger::StandaloneLogger,
    lookup::{Data, LookupDataManager},
    wasm::WasmHandler,
};
use rand::{rngs::SmallRng, Rng, SeedableRng};

fn bench_invoke_echo(c: &mut Criterion) {
    let test_state = create_test_state_with_wasm_module_name("echo");

    // Measure throughput for different data sizes.
    let mut group = c.benchmark_group("echo wasm");
    for size in [0, 1, 10, 100, 1000].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let data = vec![88u8; size];
            b.iter(|| {
                let response = test_state
                    .wasm_handler
                    .handle_invoke(Request {
                        body: data.to_vec(),
                    })
                    .unwrap();
                assert_eq!(response.body, data.to_vec());
            })
        });
    }
    group.finish();
}

fn bench_invoke_lookup(c: &mut Criterion) {
    let test_state = create_test_state_with_wasm_module_name("key_value_lookup");

    let max_data_size = 1000;

    let test_data = create_test_data(0, max_data_size);
    test_state
        .lookup_data_manager
        .extend_next_lookup_data(test_data.clone());
    test_state.lookup_data_manager.finish_next_lookup_data();

    c.bench_function("lookup wasm", |b| {
        let mut rng = SmallRng::seed_from_u64(0);
        let i = rng.gen_range(0..max_data_size);
        let request = format!("key{i}").into_bytes();
        let expected_response = format!("value{i}").into_bytes();
        b.iter(|| {
            let response = test_state
                .wasm_handler
                .handle_invoke(Request {
                    body: request.to_vec(),
                })
                .unwrap();
            assert_eq!(response.body, expected_response);
        })
    });

    // Baseline for comparison.
    c.bench_function("lookup native", |b| {
        let mut rng = SmallRng::seed_from_u64(0);
        let i = rng.gen_range(0..max_data_size);
        let request: Bytes = format!("key{i}").into_bytes().into();
        let expected_response = format!("value{i}").into_bytes();
        b.iter(|| {
            let response = test_data.get(&request).unwrap();
            assert_eq!(response.as_ref(), expected_response);
        })
    });
}

fn create_test_data(start: i32, end: i32) -> Data {
    HashMap::from_iter((start..end).map(|i| {
        (
            format!("key{}", i).into_bytes().into(),
            format!("value{}", i).into_bytes().into(),
        )
    }))
}

struct TestState {
    wasm_handler: WasmHandler,
    lookup_data_manager: Arc<LookupDataManager>,
}

fn create_test_state_with_wasm_module_name(wasm_module_name: &str) -> TestState {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(HashMap::new(), logger.clone()));
    let wasm_module_path =
        oak_functions_test_utils::build_rust_crate_wasm(wasm_module_name).unwrap();
    let wasm_module_bytes = std::fs::read(wasm_module_path).unwrap();

    let wasm_handler = oak_functions_service::wasm::new_wasm_handler(
        &wasm_module_bytes,
        lookup_data_manager.clone(),
        None,
    )
    .unwrap();

    TestState {
        wasm_handler,
        lookup_data_manager,
    }
}

criterion_group!(benches, bench_invoke_echo, bench_invoke_lookup);
criterion_main!(benches);
