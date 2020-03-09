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

use crate::proto::aggregator::Vector;
use assert_matches::assert_matches;
use oak::grpc;
use protobuf::well_known_types::Empty;

const MODULE_CONFIG_NAME: &str = "aggregator";

fn submit_sample(
    runtime: &oak_runtime::RuntimeRef,
    entry_channel: &oak_runtime::ChannelWriter,
    items: Vec<u64>,
) {
    let req = Vector {
        items,
        ..Default::default()
    };
    let result: grpc::Result<Empty> = oak_tests::grpc_request(
        runtime,
        &entry_channel,
        "/oak.examples.aggregator.Aggregator/SubmitSample",
        req,
    );
    assert_matches!(result, Ok(_));
}

#[test]
fn test_aggregator() {
    simple_logger::init().unwrap();

    let (runtime, entry_channel) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    submit_sample(&runtime, &entry_channel, vec![0, 1, 0, 1, 0]);
    submit_sample(&runtime, &entry_channel, vec![1, 0, 1, 0, 1]);
    {
        let req = Empty::new();
        let result: grpc::Result<Vector> = oak_tests::grpc_request(
            &runtime,
            &entry_channel,
            "/oak.examples.aggregator.Aggregator/GetCurrentValue",
            req,
        );
        assert_matches!(result, Err(_));
    }

    submit_sample(&runtime, &entry_channel, vec![1, 1, 1, 1, 1]);
    {
        let req = Empty::new();
        let result: grpc::Result<Vector> = oak_tests::grpc_request(
            &runtime,
            &entry_channel,
            "/oak.examples.aggregator.Aggregator/GetCurrentValue",
            req,
        );
        assert_matches!(result, Ok(_));
        assert_eq!(vec![2, 2, 2, 2, 2], result.unwrap().items);
    }

    runtime.stop();
}
