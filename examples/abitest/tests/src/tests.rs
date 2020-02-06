//
// Copyright 2019 The Project Oak Authors
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

use abitest_0_frontend::proto::abitest::{ABITestRequest, ABITestResponse};
use assert_matches::assert_matches;
use log::{error, info};
use oak::grpc;

// Constants for Node config names that should match those in the textproto
// config held in ../../client/config.h.
const FRONTEND_CONFIG_NAME: &str = "frontend-config";
const BACKEND_CONFIG_NAME: &str = "backend-config";
const LOG_CONFIG_NAME: &str = "logging-config";
const FRONTEND_ENTRYPOINT_NAME: &str = "frontend_oak_main";

// TODO(#541)
const FRONTEND_WASM: &str = "../../target/wasm32-unknown-unknown/debug/abitest_0_frontend.wasm";
const BACKEND_WASM: &str = "../../target/wasm32-unknown-unknown/debug/abitest_1_backend.wasm";

#[test]
fn test_abi() {
    simple_logger::init().unwrap();

    let configuration = oak_tests::test_configuration(
        &[
            (FRONTEND_CONFIG_NAME, FRONTEND_WASM),
            (BACKEND_CONFIG_NAME, BACKEND_WASM),
        ],
        LOG_CONFIG_NAME,
        FRONTEND_CONFIG_NAME,
        FRONTEND_ENTRYPOINT_NAME,
    );
    let (runtime, entry_channel) = oak_runtime::Runtime::configure_and_run(configuration)
        .expect("Unable to configure runtime with test wasm!");

    let result: grpc::Result<ABITestResponse> = oak_tests::grpc_request(
        &entry_channel,
        "/oak.examples.abitest.OakABITestService/RunTests",
        ABITestRequest::new(),
    );
    assert_matches!(result, Ok(_));

    runtime.stop();

    for result in result.unwrap().get_results() {
        info!(
            "[ {} ] {}",
            if result.success { " OK " } else { "FAIL" },
            result.name
        );
        if !result.success {
            error!("Failure details: {}", result.details);
        }
        assert_eq!(true, result.success);
    }
}
