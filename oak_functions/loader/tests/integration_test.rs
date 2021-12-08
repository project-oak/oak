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

use futures::executor::block_on;
use maplit::hashmap;
use oak_functions_abi::proto::Request;
use oak_functions_loader::{
    logger::Logger,
    lookup::{LookupData, LookupDataSource},
    server::WasmHandler,
};
use once_cell::sync::Lazy;
use std::{io::Write, sync::Arc};
use tokio;

static WASM_MODULE_BYTES: Lazy<Vec<u8>> = Lazy::new(|| {
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("tests");
    manifest_path.push("module");
    manifest_path.push("Cargo.toml");

    test_utils::compile_rust_wasm(manifest_path.to_str().unwrap(), false)
        .expect("Could not read Wasm module")
});

#[tokio::test]
async fn test_consistent_lookup() {
    let entries = hashmap! {
       b"ConsistentLookup".to_vec() => b"Value1".to_vec(),
    };
    let serialized_entries = test_utils::serialize_entries(entries);
    let temp_file = tempfile::NamedTempFile::new().unwrap();
    temp_file.as_file().write_all(&serialized_entries).unwrap();

    let lookup_data = Arc::new(crate::LookupData::new_empty(
        Some(LookupDataSource::File(temp_file.path().to_path_buf())),
        Logger::for_test(),
    ));
    let _ = block_on(lookup_data.refresh());

    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        lookup_data.clone(),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"ConsistentLookup".to_vec(),
    };

    let response = wasm_handler.handle_invoke(request.clone()).await.unwrap();
    assert_eq!(response.body().unwrap(), b"Value1");

    // Now we update the entries and refresh the lookup_data.
    let entries = hashmap! {
       b"ConsistentLookup".to_vec() => b"Value2".to_vec(),
    };
    let serialized_entries = test_utils::serialize_entries(entries);
    temp_file.as_file().write_all(&serialized_entries).unwrap();
    let _ = block_on(lookup_data.refresh());

    // A second Wasm module created at this point would expect the new lookup data.
    let wasm_handler2 = WasmHandler::create(
        &WASM_MODULE_BYTES,
        lookup_data.clone(),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");
    let response = wasm_handler2.handle_invoke(request.clone()).await.unwrap();
    assert_eq!(response.body().unwrap(), b"Value2");

    // Even though the lookup data was refreshed in the background
    // we expect the same result during the lifetime of the first Wasm module.
    let response = wasm_handler.handle_invoke(request.clone()).await.unwrap();
    assert_eq!(response.body().unwrap(), b"Value1");
}
