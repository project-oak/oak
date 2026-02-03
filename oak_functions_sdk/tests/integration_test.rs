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

use std::sync::Arc;

use lazy_static::lazy_static;
use oak_file_utils::data_path;
use oak_functions_abi::{Request, Response};
use oak_functions_service::{
    Handler,
    logger::StandaloneLogger,
    lookup::LookupDataManager,
    wasm::{WasmHandler, api::StdWasmApiFactory},
};

lazy_static! {
    static ref LOOKUP_WASM_MODULE_BYTES: Vec<u8> = {
        let wasm_path = data_path("oak_functions_sdk/tests/lookup_module/lookup_module.wasm");
        std::fs::read(wasm_path).expect("couldn't read compiled module")
    };
    static ref TESTING_WASM_MODULE_BYTES: Vec<u8> = {
        let wasm_path = data_path("oak_functions_sdk/tests/testing_module/testing_module.wasm");
        std::fs::read(wasm_path).expect("couldn't read compiled module")
    };
}

#[tokio::test]
async fn test_read_write() {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"ReadWrite".to_vec() };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "ReadWriteResponse");
}

#[tokio::test]
async fn test_double_read() {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"DoubleRead".to_vec() };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "DoubleReadResponse");
}

#[tokio::test]
async fn test_double_write() {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"DoubleWrite".to_vec() };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "DoubleWriteResponse");
}

#[tokio::test]
async fn test_write_log() {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"WriteLog".to_vec() };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "WriteLogResponse");
}

#[tokio::test]
async fn test_storage_get_item() {
    let entries = Vec::from_iter([(b"StorageGet".to_vec(), b"StorageGetResponse".to_vec())]);

    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager = Arc::new(LookupDataManager::<1>::for_test(entries, logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"StorageGet".to_vec() };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "StorageGetResponse");
}

#[tokio::test]
async fn test_storage_get_item_not_found() {
    // empty lookup data, no key will be found
    let entries = Vec::default();

    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager = Arc::new(LookupDataManager::<1>::for_test(entries, logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"StorageGetItemNotFound".to_vec() };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "No item found");
}

#[tokio::test]
#[ignore]
async fn test_storage_get_item_huge_key() {
    let bytes: Vec<u8> = vec![42u8; 1 << 20];
    let entries = Vec::from_iter([(bytes.clone(), bytes.clone())]);

    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager = Arc::new(LookupDataManager::<1>::for_test(entries, logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: b"LargeKey".to_vec() };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    assert_eq!(response.body, bytes)
}

#[tokio::test]
async fn test_echo() {
    let logger = Arc::new(StandaloneLogger);
    let message_to_echo = "ECHO";

    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&TESTING_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: message_to_echo.as_bytes().to_vec() };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, message_to_echo);
}

#[tokio::test]
async fn test_blackhole() {
    // Keep in sync with
    // `workspace/oak_functions/sdk/oak_functions/tests/testing_module/src/lib.rs`.

    let logger = Arc::new(StandaloneLogger);
    let message_to_blackhole = "BLACKHOLE";

    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&TESTING_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: message_to_blackhole.as_bytes().to_vec() };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    oak_functions_test_utils::assert_response_body(response, "Blackholed");
}

#[tokio::test]
#[ignore]
async fn test_huge_response() {
    // Keep in sync with
    // `workspace/oak_functions/sdk/oak_functions/tests/testing_module/src/lib.rs`.

    let logger = Arc::new(StandaloneLogger);

    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory = StdWasmApiFactory { lookup_data_manager };

    let wasm_handler =
        WasmHandler::create(&TESTING_WASM_MODULE_BYTES, Arc::new(api_factory), logger, None)
            .expect("couldn't instantiate WasmHandler");

    let request = Request { body: "HUGE_RESPONSE".as_bytes().to_vec() };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    assert_eq!(response.body, vec![42u8; 1 << 20])
}
