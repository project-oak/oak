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
use maplit::{btreemap, hashmap};
use oak_functions_abi::proto::{Request, Response};
use oak_functions_loader::{logger::Logger, server::WasmHandler};
use oak_functions_lookup::{LookupDataManager, LookupFactory};
use oak_functions_metrics::{BucketConfig, PrivateMetricsConfig, PrivateMetricsProxyFactory};
use oak_functions_tf_inference::{read_model_from_path, TensorFlowFactory, TensorFlowModelConfig};

use std::{path::PathBuf, sync::Arc};

lazy_static! {
    static ref PATH_TO_MODULES: PathBuf = {
        // WORKSPACE_ROOT is set in .cargo/config.toml.
         [env!("WORKSPACE_ROOT"),"oak_functions", "sdk", "oak_functions", "tests"].iter().collect()
    };
    static ref LOOKUP_WASM_MODULE_BYTES: Vec<u8> = {
        let mut manifest_path = PATH_TO_MODULES.clone();
        manifest_path.push("lookup_module");
        manifest_path.push("Cargo.toml");

        test_utils::compile_rust_wasm(manifest_path.to_str().unwrap(), false)
            .expect("Could not read Wasm module")
    };
    static ref TESTING_WASM_MODULE_BYTES: Vec<u8> = {
        let mut manifest_path = PATH_TO_MODULES.clone();
        manifest_path.push("testing_module");
        manifest_path.push("Cargo.toml");

        test_utils::compile_rust_wasm(manifest_path.to_str().unwrap(), false)
            .expect("Could not read Wasm module")
    };
    static ref METRICS_WASM_MODULE_BYTES: Vec<u8> = {
        let mut manifest_path = PATH_TO_MODULES.clone();
        manifest_path.push("metrics_module");
        manifest_path.push("Cargo.toml");

        test_utils::compile_rust_wasm(manifest_path.to_str().unwrap(), false)
            .expect("Could not read Wasm module")
    };
    static ref TF_WASM_MODULE_BYTES: Vec<u8> = {
        let mut manifest_path = PATH_TO_MODULES.clone();
        manifest_path.push("tf_module");
        manifest_path.push("Cargo.toml");

        test_utils::compile_rust_wasm(manifest_path.to_str().unwrap(), false)
            .expect("Could not read Wasm module")
    };
}

#[tokio::test]
async fn test_read_write() {
    let logger = Logger::for_test();
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(hashmap! {}, logger.clone()));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, vec![lookup_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"ReadWrite".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "ReadWriteResponse");
}

#[tokio::test]
async fn test_double_read() {
    let logger = Logger::for_test();
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(hashmap! {}, logger.clone()));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, vec![lookup_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"DoubleRead".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "DoubleReadResponse");
}

#[tokio::test]
async fn test_double_write() {
    let logger = Logger::for_test();
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(hashmap! {}, logger.clone()));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, vec![lookup_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"DoubleWrite".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "DoubleWriteResponse");
}

#[tokio::test]
async fn test_write_log() {
    let logger = Logger::for_test();
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(hashmap! {}, logger.clone()));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, vec![lookup_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"WriteLog".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "WriteLogResponse");
}

#[tokio::test]
async fn test_storage_get_item() {
    let entries = hashmap! {
       b"StorageGet".to_vec() => b"StorageGetResponse".to_vec(),
    };

    let logger = Logger::for_test();
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(entries, logger.clone()));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, vec![lookup_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"StorageGet".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "StorageGetResponse");
}

#[tokio::test]
async fn test_storage_get_item_not_found() {
    // empty lookup data, no key will be found
    let entries = hashmap! {};

    let logger = Logger::for_test();
    let lookup_data_manager = Arc::new(LookupDataManager::for_test(entries, logger.clone()));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data_manager)
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&LOOKUP_WASM_MODULE_BYTES, vec![lookup_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"StorageGetItemNotFound".to_vec(),
    };
    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "No item found");
}

#[tokio::test]
async fn test_echo() {
    let logger = Logger::for_test();
    let message_to_echo = "ECHO";

    let testing_factory =
        oak_functions_loader::testing::TestingFactory::new_boxed_extension_factory(logger.clone())
            .expect("Fail to create testing extension factory.");

    let wasm_handler =
        WasmHandler::create(&TESTING_WASM_MODULE_BYTES, vec![testing_factory], logger)
            .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: message_to_echo.as_bytes().to_vec(),
    };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, message_to_echo);
}

#[tokio::test]
async fn test_blackhole() {
    // Keep in sync with
    // `workspace/oak_functions/sdk/oak_functions/tests/testing_module/src/lib.rs`.

    let logger = Logger::for_test();
    let message_to_blackhole = "BLACKHOLE";

    let testing_factory =
        oak_functions_loader::testing::TestingFactory::new_boxed_extension_factory(logger.clone())
            .expect("Fail to create testing extension factory.");

    let wasm_handler =
        WasmHandler::create(&TESTING_WASM_MODULE_BYTES, vec![testing_factory], logger)
            .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: message_to_blackhole.as_bytes().to_vec(),
    };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "Blackholed");
}

#[tokio::test]
async fn test_report_metric() {
    let logger = Logger::for_test();

    // Keep in sync with
    // `workspace/oak_functions/sdk/oak_functions/tests/metrics_module/src/lib.rs`.
    let label = "a";
    let metrics_config = PrivateMetricsConfig {
        epsilon: 1.0,
        batch_size: 1,
        buckets: btreemap![
            label.to_string() => BucketConfig::Count,
        ],
    };

    let metrics_factory =
        PrivateMetricsProxyFactory::new_boxed_extension_factory(&metrics_config, logger.clone())
            .expect("Fail to create metrics factory.");

    let wasm_handler =
        WasmHandler::create(&METRICS_WASM_MODULE_BYTES, vec![metrics_factory], logger)
            .expect("Could not instantiate WasmHandler.");

    // The request is ignored in the Wasm module.
    let request = Request {
        body: b"_".to_vec(),
    };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    // Keep in sync with
    // `workspace/oak_functions/sdk/oak_functions/tests/metrics_module/src/lib.rs`.
    test_utils::assert_response_body(response, "MetricReported");

    // TODO(#2646): Check in the runtime that the metric was reported there.
}

#[tokio::test]
async fn test_tf_model_infer_bad_input() {
    let logger = Logger::for_test();

    // Re-use path and share from oak_functions/examples/mobilenet.
    let path: PathBuf = [
        env!("WORKSPACE_ROOT"),
        "oak_functions",
        "examples",
        "mobilenet",
        "files",
        "mobilenet_v2_1.4_224_frozen.pb",
    ]
    .iter()
    .collect();
    let shape = vec![1, 224, 224, 3];

    let tf_model_config = TensorFlowModelConfig {
        path: path.into_os_string().into_string().unwrap(),
        shape,
    };

    let model = read_model_from_path(&tf_model_config.path).expect("Fail to read model.");

    let tf_factory = TensorFlowFactory::new_boxed_extension_factory(
        model,
        tf_model_config.shape,
        logger.clone(),
    )
    .expect("Fail to create tf factory.");

    let wasm_handler = WasmHandler::create(&TF_WASM_MODULE_BYTES, vec![tf_factory], logger)
        .expect("Could not instantiate WasmHandler.");

    let request = Request {
        body: b"intentionally bad input vector".to_vec(),
    };

    let response: Response = wasm_handler.handle_invoke(request).unwrap();
    test_utils::assert_response_body(response, "ErrBadTensorFlowModelInput");
}
