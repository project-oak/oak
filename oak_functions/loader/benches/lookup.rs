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
//

pub mod proto {
    tonic::include_proto!("oak.functions.benchmark");
}

use criterion::{
    criterion_group, criterion_main, measurement::Measurement, AxisScale, BenchmarkGroup,
    BenchmarkId, Criterion, PlotConfiguration,
};
use lookup_data_generator::data::generate_and_serialize_random_entries;
use oak_functions_abi::proto::{Request, StatusCode};
use oak_functions_loader::{
    logger::Logger,
    lookup::LookupFactory,
    lookup_data::{parse_lookup_entries, LookupData},
    server::WasmHandler,
};
use prost::Message;
use proto::{benchmark_request::Action, BenchmarkRequest, LookupTest};
use rand::SeedableRng;
use std::{collections::HashMap, sync::Arc};
use tokio::runtime::Runtime;

const MANIFEST_PATH: &str = "examples/benchmark/module/Cargo.toml";
const SINGLE_REQUEST_ITERATIONS: u32 = 1;
const MULTI_REQUEST_ITERATIONS: u32 = 101;

fn key_size(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let wasm_module_bytes = build_wasm_module(MANIFEST_PATH);

    let mut group = c.benchmark_group("key_size");
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    group.plot_config(plot_config);
    for size in [16usize, 128usize, 1_024usize] {
        let TestData {
            test_key,
            expected_value,
            entries,
        } = generate_random_test_data_for_bench(size, 256, 1_000);
        run_benchmarks_with_input(
            &rt,
            &mut group,
            &wasm_module_bytes,
            entries,
            &test_key,
            &expected_value,
            size,
        );
    }
    group.finish();
}

fn value_size(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let wasm_module_bytes = build_wasm_module(MANIFEST_PATH);

    let mut group = c.benchmark_group("value_size");
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    group.plot_config(plot_config);
    for size in [16usize, 128usize, 1_024usize, 8_192usize] {
        let TestData {
            test_key,
            expected_value,
            entries,
        } = generate_random_test_data_for_bench(32, size, 1_000);
        run_benchmarks_with_input(
            &rt,
            &mut group,
            &wasm_module_bytes,
            entries,
            &test_key,
            &expected_value,
            size,
        );
    }
    group.finish();
}

fn entry_count(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let wasm_module_bytes = build_wasm_module(MANIFEST_PATH);

    let mut group = c.benchmark_group("entry_count");
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    group.plot_config(plot_config);
    for count in [100usize, 10_000usize, 1_000_000usize] {
        let TestData {
            test_key,
            expected_value,
            entries,
        } = generate_random_test_data_for_bench(64, 256, count);
        run_benchmarks_with_input(
            &rt,
            &mut group,
            &wasm_module_bytes,
            entries,
            &test_key,
            &expected_value,
            count,
        );
    }
    group.finish();
}

criterion_group!(benches, key_size, value_size, entry_count);
criterion_main!(benches);

fn run_benchmarks_with_input<M: Measurement>(
    rt: &Runtime,
    group: &mut BenchmarkGroup<M>,
    wasm_module_bytes: &[u8],
    lookup_entries: HashMap<Vec<u8>, Vec<u8>>,
    test_key: &[u8],
    expected_value: &[u8],
    size: usize,
) {
    let lookup_data = Arc::new(LookupData::for_test(lookup_entries));
    let logger = Logger::for_test();
    let lookup_factory = LookupFactory::create(lookup_data, logger.clone()).unwrap();

    let wasm_handler = WasmHandler::create(wasm_module_bytes, vec![lookup_factory], logger)
        .expect("Couldn't create the server");

    let single_benchmark_request = BenchmarkRequest {
        iterations: SINGLE_REQUEST_ITERATIONS,
        action: Some(Action::Lookup(LookupTest {
            key: test_key.to_owned(),
        })),
    }
    .encode_to_vec();
    let multi_benchmark_request = BenchmarkRequest {
        iterations: MULTI_REQUEST_ITERATIONS,
        action: Some(Action::Lookup(LookupTest {
            key: test_key.to_owned(),
        })),
    }
    .encode_to_vec();

    group.bench_with_input(BenchmarkId::new("single", size), &size, |b, _size| {
        b.iter(|| {
            run_lookup_iteration(rt, &wasm_handler, &single_benchmark_request, expected_value)
        })
    });
    group.bench_with_input(BenchmarkId::new("multi", size), &size, |b, _size| {
        b.iter(|| run_lookup_iteration(rt, &wasm_handler, &multi_benchmark_request, expected_value))
    });
}

fn run_lookup_iteration(
    rt: &Runtime,
    wasm_handler: &WasmHandler,
    benchmark_request: &[u8],
    expected_value: &[u8],
) {
    let request = Request {
        body: benchmark_request.to_owned(),
    };
    let resp = rt.block_on(wasm_handler.handle_invoke(request)).unwrap();
    assert_eq!(resp.status, StatusCode::Success as i32);
    assert_eq!(&resp.body, expected_value);
}

/// The test data used for benchmarking.
struct TestData {
    /// The key to use for doing lookups.
    test_key: Vec<u8>,
    /// The expected value returned when doing a lookup.
    expected_value: Vec<u8>,
    /// The lookup data entries.
    entries: HashMap<Vec<u8>, Vec<u8>>,
}

fn generate_random_test_data_for_bench(
    key_size_bytes: usize,
    value_size_bytes: usize,
    entry_count: usize,
) -> TestData {
    // Use a fixed RNG so results are reproducible.
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    let buf = generate_and_serialize_random_entries(
        &mut rng,
        key_size_bytes,
        value_size_bytes,
        entry_count,
    )
    .unwrap();
    let entries = parse_lookup_entries(buf).unwrap();
    let (key, value) = entries.iter().next().unwrap();
    TestData {
        test_key: key.to_vec(),
        expected_value: value.to_vec(),
        entries,
    }
}

fn build_wasm_module(relative_path: &str) -> Vec<u8> {
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(relative_path);
    test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
        .expect("Couldn't read Wasm module")
}
