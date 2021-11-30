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

use lazy_static;
use maplit::hashmap;
use oak_functions_abi::proto::{Request, Response};
use oak_functions_loader::{logger::Logger, lookup::LookupData, server::WasmHandler};
use std::sync::Arc;
use tokio;

lazy_static::lazy_static! {
    static ref RUNTIME: tokio::runtime::Runtime = tokio::runtime::Runtime::new().unwrap();
}

#[test]
fn test_sdk() {
    let manifest_path = "/workspace/oak_functions/sdk/oak_functions/tests/module/Cargo.toml";

    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path, false).expect("Could not read Wasm module");

    let entries = hashmap! {
       b"StorageGet".to_vec() => b"StorageGetResponse".to_vec(),
    };

    let wasm_handler = WasmHandler::create(
        &wasm_module_bytes,
        Arc::new(LookupData::for_test(entries)),
        vec![],
        Logger::for_test(),
    )
    .expect("Could not instantiate WasmHandler.");

    let tests = hashmap! [
        "ReadWrite" => "ReadWriteResponse",
        "DoubleRead" => "DoubleReadResponse",
        "DoubleWrite" => "DoubleWriteResponse",
        "WriteLog" => "WriteLogResponse",
        "StorageGet" => "StorageGetResponse",
    ];

    for (request_body, expected_response_body) in tests {
        let request = Request {
            body: request_body.as_bytes().to_vec(),
        };
        let response: Result<Response, _> = RUNTIME.block_on(wasm_handler.handle_invoke(request));

        let actual_response_body: String = {
            let rb = response.unwrap().body;
            String::from_utf8(rb).unwrap()
        };
        assert_eq!(actual_response_body, expected_response_body);
    }
}
