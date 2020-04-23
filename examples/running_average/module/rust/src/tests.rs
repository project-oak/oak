//
// Copyright 2020 The Project Oak Authors
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

use crate::proto::{GetAverageResponse, SubmitSampleRequest};
use assert_matches::assert_matches;
use oak::grpc;

const MODULE_CONFIG_NAME: &str = "running_average";

fn submit_sample(runtime: &oak_runtime::RuntimeProxy, entry_handle: oak_abi::Handle, value: u64) {
    let req = SubmitSampleRequest { value };
    let result: grpc::Result<()> = oak_tests::grpc_request(
        &runtime,
        entry_handle,
        "/oak.examples.running_average.RunningAverage/SubmitSample",
        &req,
    );
    assert_matches!(result, Ok(_));
}

#[test]
fn test_running_average() {
    simple_logger::init().unwrap();

    let (runtime, entry_handle) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    submit_sample(&runtime, entry_handle, 100);
    submit_sample(&runtime, entry_handle, 200);

    let result: grpc::Result<GetAverageResponse> = oak_tests::grpc_request(
        &runtime,
        entry_handle,
        "/oak.examples.running_average.RunningAverage/GetAverage",
        &(),
    );
    assert_matches!(result, Ok(_));
    assert_eq!(150, result.unwrap().average);

    runtime.stop_runtime();
}
