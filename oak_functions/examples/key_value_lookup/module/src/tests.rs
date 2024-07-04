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

// This is only needed in bazel because it considers the `tests.rs` file as a
// separate crate.
#![cfg_attr(feature = "bazel", feature(test))]

extern crate test;

use std::time::Duration;

use maplit::hashmap;
use oak_client::verifier::InsecureAttestationVerifier;
use oak_functions_client::OakFunctionsClient;
use oak_functions_test_utils::make_request;
use test::Bencher;

#[tokio::test]
async fn test_server() {
    // TODO: b/349587445 - Remove bazel exclusion once dependencies are bazelified.
    if xtask::testing::skip_test() || cfg!(feature = "bazel") {
        log::info!("skipping test");
        return;
    }

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup").unwrap();

    let lookup_data_file = oak_functions_test_utils::write_to_temp_file(
        &oak_functions_test_utils::serialize_entries(hashmap! {
            b"key_0".to_vec() => b"value_0".to_vec(),
            b"key_1".to_vec() => b"value_1".to_vec(),
            b"key_2".to_vec() => b"value_2".to_vec(),
            b"empty".to_vec() => vec![],
        }),
    );

    // TODO: b/349587445 - Use bazel variant once dependencies are bazelified.
    let (_server_background, server_port) =
        xtask::launcher::run_oak_functions_example_in_background(
            &wasm_path,
            lookup_data_file.path().to_str().unwrap(),
        )
        .await;

    // Wait for the server to start up.
    // TODO(#4677): Reduce the wait time.
    std::thread::sleep(Duration::from_secs(15));

    {
        // Lookup match.
        let response = make_request(server_port, b"key_1").await;
        assert_eq!(b"value_1", &response.as_ref());
    }
    {
        // Lookup fail.
        let response = make_request(server_port, b"key_42").await;
        assert_eq!(Vec::<u8>::new(), response);
    }
    {
        // Lookup match but empty value.
        let response = make_request(server_port, b"empty").await;
        assert_eq!(Vec::<u8>::new(), response);
    }
}

#[bench]
fn bench_wasm_handler(bencher: &mut Bencher) {
    // TODO: b/349587445 - Remove bazel exclusion once dependencies are bazelified.
    if xtask::testing::skip_test() || cfg!(feature = "bazel") {
        log::info!("skipping test");
        return;
    }

    let runtime =
        tokio::runtime::Builder::new_current_thread().enable_io().enable_time().build().unwrap();

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup").unwrap();

    let lookup_data_file = oak_functions_test_utils::write_to_temp_file(
        &oak_functions_test_utils::serialize_entries(hashmap! {
            b"key_0".to_vec() => b"value_0".to_vec(),
            b"key_1".to_vec() => b"value_1".to_vec(),
            b"key_2".to_vec() => b"value_2".to_vec(),
            b"empty".to_vec() => vec![],
        }),
    );

    let (_server_background, server_port) =
        runtime.block_on(xtask::launcher::run_oak_functions_example_in_background(
            &wasm_path,
            lookup_data_file.path().to_str().unwrap(),
        ));

    // Wait for the server to start up.
    std::thread::sleep(Duration::from_secs(20));

    let uri = format!("http://localhost:{server_port}/");
    let mut client = runtime
        .block_on(OakFunctionsClient::new(&uri, &InsecureAttestationVerifier))
        .expect("couldn't create client");

    let summary = bencher.bench(|bencher| {
        bencher.iter(|| {
            let response = runtime.block_on(client.invoke(b"key_1"));
            assert_eq!(b"value_1", &response.unwrap().as_ref());
        });
        Ok(())
    });

    // When running `cargo test` this benchmark test gets executed too, but
    // `summary` will be `None` in that case. So, here we first check that
    // `summary` is not empty.
    if let Ok(Some(summary)) = summary {
        // `summary.mean` is in nanoseconds, even though it is not explicitly documented
        // in https://doc.rust-lang.org/test/stats/struct.Summary.html.
        let elapsed = Duration::from_nanos(summary.mean as u64);
        // We expect the `mean` time for loading the test Wasm module and running its
        // main function to be less than a fixed threshold.
        assert!(elapsed < Duration::from_millis(5), "elapsed time: {:.0?}", elapsed);
    }
}
