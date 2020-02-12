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

use crate::proto::running_average::{GetAverageResponse, SubmitSampleRequest};
use assert_matches::assert_matches;
use oak::grpc;
use protobuf::well_known_types::Empty;

const MODULE_CONFIG_NAME: &str = "running_average";

fn submit_sample(entry_channel: &oak_runtime::ChannelWriter, value: u64) {
    let mut req = SubmitSampleRequest::new();
    req.value = value;
    let result: grpc::Result<Empty> = oak_tests::grpc_request(
        &entry_channel,
        "/oak.examples.running_average.RunningAverage/SubmitSample",
        req,
    );
    assert_matches!(result, Ok(_));
}

#[test]
fn test_running_average() {
    simple_logger::init().unwrap();

    let (runtime, entry_channel) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    submit_sample(&entry_channel, 100);
    submit_sample(&entry_channel, 200);

    let req = Empty::new();
    let result: grpc::Result<GetAverageResponse> = oak_tests::grpc_request(
        &entry_channel,
        "/oak.examples.running_average.RunningAverage/GetAverage",
        req,
    );
    assert_matches!(result, Ok(_));
    assert_eq!(150, result.unwrap().average);

    runtime.stop();
}
