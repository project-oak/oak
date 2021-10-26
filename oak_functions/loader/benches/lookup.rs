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

#![feature(test)]

extern crate test;

pub mod proto {
    tonic::include_proto!("oak.functions.benchmark");
}

use lookup_data_generator::data::generate_and_serialize_random_entries;
use maplit::hashmap;
use oak_functions_abi::proto::{Request, StatusCode};
use oak_functions_loader::{
    logger::Logger,
    lookup::{parse_lookup_entries, LookupData},
    server::WasmHandler,
};
use prost::Message;
use proto::{benchmark_request::Action, BenchmarkRequest, LookupTest};
use std::{collections::HashMap, sync::Arc, time::Duration};
use test::Bencher;

const MANIFEST_PATH: &str = "examples/benchmark/module/Cargo.toml";

#[bench]
fn small_fixed_data_single_lookup(bencher: &mut Bencher) {
    let entries = hashmap! {
        b"key_0".to_vec() => br#"value_0"#.to_vec(),
        b"key_1".to_vec() => br#"value_1"#.to_vec(),
        b"key_2".to_vec() => br#"value_2"#.to_vec(),
    };

    let test_data = TestData {
        key: br#"key_1"#.to_vec(),
        value: br#"value_1"#.to_vec(),
        entries,
    };

    run_lookup_bench(bencher, test_data, 1, Duration::from_millis(5));
}

#[bench]
fn small_fixed_data_multi_lookup(bencher: &mut Bencher) {
    let entries = hashmap! {
        b"key_0".to_vec() => br#"value_0"#.to_vec(),
        b"key_1".to_vec() => br#"value_1"#.to_vec(),
        b"key_2".to_vec() => br#"value_2"#.to_vec(),
    };

    let test_data = TestData {
        key: br#"key_1"#.to_vec(),
        value: br#"value_1"#.to_vec(),
        entries,
    };

    run_lookup_bench(bencher, test_data, 101, Duration::from_millis(10));
}

#[bench]
fn small_random_data_single_lookup(bencher: &mut Bencher) {
    let test_data = generate_random_test_data_for_bench(16, 16, 20);

    run_lookup_bench(bencher, test_data, 1, Duration::from_millis(5));
}

#[bench]
fn small_random_data_multi_lookup(bencher: &mut Bencher) {
    let test_data = generate_random_test_data_for_bench(16, 16, 20);

    run_lookup_bench(bencher, test_data, 101, Duration::from_millis(10));
}

#[bench]
fn medium_random_data_single_lookup(bencher: &mut Bencher) {
    let test_data = generate_random_test_data_for_bench(128, 256, 200_000);

    run_lookup_bench(bencher, test_data, 1, Duration::from_millis(5));
}

#[bench]
fn medium_random_data_multi_lookup(bencher: &mut Bencher) {
    let test_data = generate_random_test_data_for_bench(128, 256, 200_000);

    run_lookup_bench(bencher, test_data, 101, Duration::from_millis(10));
}

#[bench]
fn large_random_data_single_lookup(bencher: &mut Bencher) {
    let test_data = generate_random_test_data_for_bench(1_024, 10_240, 1_000_000);

    run_lookup_bench(bencher, test_data, 1, Duration::from_millis(5));
}

#[bench]
fn large_random_data_multi_lookup(bencher: &mut Bencher) {
    let test_data = generate_random_test_data_for_bench(1_024, 10_240, 1_000_000);

    run_lookup_bench(bencher, test_data, 101, Duration::from_millis(25));
}

fn run_lookup_bench(bencher: &mut Bencher, test_data: TestData, iterations: u32, cutoff: Duration) {
    let wasm_module_bytes = bulid_wasm_module(MANIFEST_PATH);
    let lookup_data = Arc::new(LookupData::for_test(test_data.entries));
    let benchmark_request = BenchmarkRequest {
        iterations,
        action: Some(Action::Lookup(LookupTest { key: test_data.key })),
    };
    let value = test_data.value;
    let logger = Logger::for_test();
    let wasm_handler = WasmHandler::create(&wasm_module_bytes, lookup_data, vec![], logger)
        .expect("Couldn't create the server");
    let rt = tokio::runtime::Runtime::new().unwrap();

    let summary = bencher
        .bench(|bencher| {
            bencher.iter(|| {
                let request = Request {
                    body: benchmark_request.encode_to_vec(),
                };
                let resp = rt
                    .block_on(wasm_handler.clone().handle_invoke(request))
                    .unwrap();
                assert_eq!(resp.status, StatusCode::Success as i32);
                assert_eq!(resp.body, value);
            });
        })
        .unwrap();

    // `summary.mean` is in nanoseconds, even though it is not explicitly documented in
    // https://doc.rust-lang.org/test/stats/struct.Summary.html.
    let elapsed = Duration::from_nanos(summary.mean as u64);
    // We expect the `mean` time for loading the test Wasm module and running its main function
    // to be less than a fixed threshold.
    assert!(elapsed <= cutoff, "elapsed time: {:.0?}", elapsed);
}

struct TestData {
    key: Vec<u8>,
    value: Vec<u8>,
    entries: HashMap<Vec<u8>, Vec<u8>>,
}

fn generate_random_test_data_for_bench(
    key_size_bytes: usize,
    value_size_bytes: usize,
    entry_count: usize,
) -> TestData {
    let mut rng = rand::thread_rng();
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
        key: key.to_vec(),
        value: value.to_vec(),
        entries,
    }
}

fn bulid_wasm_module(relative_path: &str) -> Vec<u8> {
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(relative_path);
    test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
        .expect("Couldn't read Wasm module")
}
