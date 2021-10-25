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

use maplit::hashmap;
use oak_functions_abi::proto::{Request, StatusCode};
use oak_functions_loader::{
    logger::Logger,
    lookup::{parse_lookup_entries, LookupData},
    server::WasmHandler,
};
use std::{collections::HashMap, sync::Arc, time::Duration};
use test::{stats::Summary, Bencher};

const MANIFEST_PATH: &str = "examples/key_value_lookup/module/Cargo.toml";

#[bench]
fn small_fixed_lookup_data(bencher: &mut Bencher) {
    let entries = hashmap! {
        b"key_0".to_vec() => br#"value_0"#.to_vec(),
        b"key_1".to_vec() => br#"value_1"#.to_vec(),
        b"key_2".to_vec() => br#"value_2"#.to_vec(),
    };

    let summary = run_lookup_bench(bencher, entries, br#"key_1"#.to_vec());

    // `summary.mean` is in nanoseconds, even though it is not explicitly documented in
    // https://doc.rust-lang.org/test/stats/struct.Summary.html.
    let elapsed = Duration::from_nanos(summary.unwrap().mean as u64);
    // We expect the `mean` time for loading the test Wasm module and running its main function
    // to be less than a fixed threshold.
    assert!(
        elapsed < Duration::from_millis(5),
        "elapsed time: {:.0?}",
        elapsed
    );
}

fn run_lookup_bench(
    bencher: &mut Bencher,
    entries: HashMap<Vec<u8>, Vec<u8>>,
    key: Vec<u8>,
) -> Option<Summary> {
    let lookup_data = Arc::new(LookupData::for_test(entries));
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(MANIFEST_PATH);
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
            .expect("Couldn't read Wasm module");

    let logger = Logger::for_test();
    let wasm_handler = WasmHandler::create(&wasm_module_bytes, lookup_data.clone(), vec![], logger)
        .expect("Couldn't create the server");
    let rt = tokio::runtime::Runtime::new().unwrap();

    bencher.bench(|bencher| {
        bencher.iter(|| {
            let request = Request { body: key.clone() };
            let resp = rt
                .block_on(wasm_handler.clone().handle_invoke(request))
                .unwrap();
            assert_eq!(resp.status, StatusCode::Success as i32);
            assert_eq!(std::str::from_utf8(&resp.body).unwrap(), r#"value_1"#);
        });
    })
}
