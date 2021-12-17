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

use lazy_static::lazy_static;
use maplit::hashmap;
use oak_functions_abi::proto::{Request, Response};
use oak_functions_loader::{logger::Logger, lookup::LookupData, server::WasmHandler};
use std::sync::Arc;

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
async fn test_read_write() {
    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::for_test(hashmap! {})),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"ReadWrite".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).await.unwrap();
    assert_eq!(response.body().unwrap(), b"ReadWriteResponse");
}

#[tokio::test]
async fn test_double_read() {
    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::for_test(hashmap! {})),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"DoubleRead".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).await.unwrap();
    assert_eq!(response.body().unwrap(), b"DoubleReadResponse");
}

#[tokio::test]
async fn test_double_write() {
    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::for_test(hashmap! {})),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"DoubleWrite".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).await.unwrap();
    assert_eq!(response.body().unwrap(), b"DoubleWriteResponse");
}

#[tokio::test]
async fn test_write_log() {
    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::for_test(hashmap! {})),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"WriteLog".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).await.unwrap();
    assert_eq!(response.body().unwrap(), b"WriteLogResponse");
}

#[tokio::test]
async fn test_storage_get_item() {
    let entries = hashmap! {
       b"StorageGet".to_vec() => b"StorageGetResponse".to_vec(),
    };

    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::for_test(entries)),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"StorageGet".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).await.unwrap();
    assert_eq!(response.body().unwrap(), b"StorageGetResponse");
}
