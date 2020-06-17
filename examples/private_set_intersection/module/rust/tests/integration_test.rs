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

use assert_matches::assert_matches;
use private_set_intersection_grpc::proto::{
    private_set_intersection_client::PrivateSetIntersectionClient, SubmitSetRequest,
};
use std::{collections::HashSet, iter::FromIterator};

const MODULE_CONFIG_NAME: &str = "private_set_intersection";

#[tokio::test(core_threads = 2)]
async fn test_set_intersection() {
    env_logger::init();

    let runtime = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = PrivateSetIntersectionClient::with_interceptor(channel, interceptor);

    let req = SubmitSetRequest {
        values: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    };
    let result = client.submit_set(req).await;
    assert_matches!(result, Ok(_));

    let req = SubmitSetRequest {
        values: vec!["b".to_string(), "c".to_string(), "d".to_string()],
    };
    let result = client.submit_set(req).await;
    assert_matches!(result, Ok(_));

    let result = client.get_intersection(()).await;
    assert_matches!(result, Ok(_));
    let got = HashSet::<String>::from_iter(result.unwrap().into_inner().values.to_vec());
    let want: HashSet<String> = ["b".to_string(), "c".to_string()].iter().cloned().collect();
    assert_eq!(got, want);

    runtime.stop();
}
