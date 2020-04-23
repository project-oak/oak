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

use crate::proto::{GetIntersectionResponse, SubmitSetRequest};
use assert_matches::assert_matches;
use oak::grpc;
use std::{collections::HashSet, iter::FromIterator};

const MODULE_CONFIG_NAME: &str = "private_set_intersection";

#[test]
fn test_set_intersection() {
    simple_logger::init().unwrap();

    let (runtime, entry_channel) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let req = SubmitSetRequest {
        values: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    };
    let result: grpc::Result<()> = oak_tests::grpc_request(
        &runtime,
        entry_channel,
        "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet",
        &req,
    );
    assert_matches!(result, Ok(_));

    let req = SubmitSetRequest {
        values: vec!["b".to_string(), "c".to_string(), "d".to_string()],
    };
    let result: grpc::Result<()> = oak_tests::grpc_request(
        &runtime,
        entry_channel,
        "/oak.examples.private_set_intersection.PrivateSetIntersection/SubmitSet",
        &req,
    );
    assert_matches!(result, Ok(_));

    let result: grpc::Result<GetIntersectionResponse> = oak_tests::grpc_request(
        &runtime,
        entry_channel,
        "/oak.examples.private_set_intersection.PrivateSetIntersection/GetIntersection",
        &(),
    );
    assert_matches!(result, Ok(_));
    let got = HashSet::<String>::from_iter(result.unwrap().values.to_vec());
    let want: HashSet<String> = ["b".to_string(), "c".to_string()].iter().cloned().collect();
    assert_eq!(got, want);

    runtime.stop_runtime();
}
