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

extern crate test;

use location_utils::{
    cell_id_to_bytes, find_cell, location_from_degrees, location_to_bytes, S2_DEFAULT_LEVEL,
};
use lookup_data_generator::data::generate_and_serialize_sparse_weather_entries;
use maplit::hashmap;
use oak_functions_abi::StatusCode;
use rand::{prelude::StdRng, SeedableRng};
use std::time::Duration;
use test::Bencher;
use test_utils::make_request;

#[tokio::test]
async fn test_server() {
    let wasm_path = test_utils::build_rust_crate_wasm("weather_lookup").unwrap();

    let location_0 = location_from_degrees(52., -0.01);
    let location_1 = location_from_degrees(14., -12.);

    // Find the cells for the locations and generate the associated lookup index entries.
    // These are purposely large so that each location is covered by a single cell.
    let level = S2_DEFAULT_LEVEL;
    let cell_0 = find_cell(&location_0, level).unwrap();
    let cell_1 = find_cell(&location_1, level).unwrap();

    let lookup_data_file = test_utils::write_to_temp_file(&test_utils::serialize_entries(
        hashmap! {
            location_to_bytes(&location_0).to_vec() => br#"{"temperature_degrees_celsius":10}"#.to_vec(),
            location_to_bytes(&location_1).to_vec() => br#"{"temperature_degrees_celsius":42}"#.to_vec(),
            cell_id_to_bytes(&cell_0) => location_to_bytes(&location_0).to_vec(),
            cell_id_to_bytes(&cell_1) => location_to_bytes(&location_1).to_vec(),
        },
    ));

    let server_port = test_utils::free_port();
    let server_background = test_utils::create_and_start_oak_functions_server(
        server_port,
        &wasm_path,
        lookup_data_file.path().to_str().unwrap(),
    )
    .unwrap();

    // Wait for the server to start up.
    std::thread::sleep(Duration::from_secs(2));

    // Test request coordinates are defined in `oak_functions/lookup_data_generator/src/data.rs`.
    {
        // Exact key_0.
        let response = make_request(server_port, br#"{"lat":52.0,"lng":-0.01}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":10}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Close to key_0.
        let response = make_request(server_port, br#"{"lat":51.9,"lng":-0.1}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":10}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // A bit further from key_0.
        let response = make_request(server_port, br#"{"lat":51.4,"lng":-0.6}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success, response.status);
        assert_eq!(
            r#"could not find location within cutoff"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Close to key_1.
        let response = make_request(server_port, br#"{"lat":14.1,"lng":-11.9}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":42}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Far from both keys.
        let response = make_request(server_port, br#"{"lat":-10.0,"lng":10.0}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success, response.status);
        assert_eq!(
            r#"could not find index item for cell"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Malformed request.
        let response = make_request(server_port, b"invalid - JSON").await.response;
        assert_eq!(StatusCode::Success, response.status);
        assert_eq!(
            "could not deserialize request as JSON: Error(\"expected value\", line: 1, column: 1)",
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }

    test_utils::kill_process(server_background);
}

#[bench]
fn bench_wasm_handler_no_warmup(bencher: &mut Bencher) {
    bench_wasm_handler(bencher, false);
}

#[bench]
fn bench_wasm_handler_with_warmup(bencher: &mut Bencher) {
    bench_wasm_handler(bencher, true);
}

/// Run a benchmark of the wasm module, optionally performing a warup-initialisation using Wizer.
fn bench_wasm_handler(bencher: &mut Bencher, warmup: bool) {
    let entry_count = 200_000;
    let elapsed_limit_millis = 20;

    let wasm_path = test_utils::build_rust_crate_wasm("weather_lookup").unwrap();
    let wasm_module_bytes = std::fs::read(&wasm_path).expect("could not read Wasm file");
    let wasm_module_bytes = if warmup {
        wizer::Wizer::new()
            .run(&wasm_module_bytes)
            .expect("Couldn't initialise Wasm module via Wizer")
    } else {
        wasm_module_bytes
    };
    let wasm_path_after_optimization = test_utils::write_to_temp_file(&wasm_module_bytes);

    let mut rng = StdRng::seed_from_u64(42);
    let lookup_data = generate_and_serialize_sparse_weather_entries(&mut rng, entry_count).unwrap();
    let lookup_data_file = test_utils::write_to_temp_file(&lookup_data);

    let server_port = test_utils::free_port();
    let server_background = test_utils::create_and_start_oak_functions_server(
        server_port,
        wasm_path_after_optimization.path().to_str().unwrap(),
        lookup_data_file.path().to_str().unwrap(),
    )
    .unwrap();

    // Wait for the server to start up.
    std::thread::sleep(Duration::from_secs(2));

    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_io()
        .enable_time()
        .build()
        .unwrap();

    let summary = bencher.bench(|bencher| {
        bencher.iter(|| {
            let response = runtime
                .block_on(make_request(server_port, br#"{"lat":-60.1,"lng":120.1}"#))
                .response;
            assert_eq!(response.status, StatusCode::Success);
        });
        Ok(())
    });

    // When running `cargo test` this benchmark test gets executed too, but `summary` will be `None`
    // in that case. So, here we first check that `summary` is not empty.
    if let Ok(Some(summary)) = summary {
        // `summary.mean` is in nanoseconds, even though it is not explicitly documented in
        // https://doc.rust-lang.org/test/stats/struct.Summary.html.
        let elapsed = Duration::from_nanos(summary.mean as u64);
        // We expect the `mean` time for loading the test Wasm module and running its main function
        // to be less than a fixed threshold.
        assert!(
            elapsed < Duration::from_millis(elapsed_limit_millis),
            "elapsed time: {:.0?}",
            elapsed
        );
    }

    test_utils::kill_process(server_background);
}
