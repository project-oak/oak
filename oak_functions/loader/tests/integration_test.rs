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
use lazy_static::lazy_static;
use maplit::hashmap;
use oak_functions_abi::proto::{Request, Response};
use oak_functions_loader::{
    logger::Logger,
    lookup::{LookupData, LookupDataSource},
    server::WasmHandler,
};
use std::{io::Write, sync::Arc};
use tokio;

lazy_static! {
    static ref WASM_MODULE_BYTES: Vec<u8> = {
        let mut manifest_path = std::env::current_dir().unwrap();
        manifest_path.push("tests");
        manifest_path.push("module");
        manifest_path.push("Cargo.toml");

        test_utils::compile_rust_wasm(manifest_path.to_str().unwrap(), false)
            .expect("Could not read Wasm module")
    };
}

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

    let response: Response = wasm_handler.handle_invoke(request).await.unwrap();
    assert_eq!(response.body().unwrap(), b"Value1");

    let entries = hashmap! {
       b"ConsistentLookup".to_vec() => b"Value2".to_vec(),
    };
    let serialized_entries = test_utils::serialize_entries(entries);
    temp_file.as_file().write_all(&serialized_entries).unwrap();

    let _ = block_on(lookup_data.refresh());

    let request2 = Request {
        body: b"ConsistentLookup".to_vec(),
    };

    // even though the lookup data was refreshed in the backgroud
    // we expect the same in the wasm module
    let response2: Response = wasm_handler.handle_invoke(request2).await.unwrap();
    assert_eq!(response2.body().unwrap(), b"Value1");
}
