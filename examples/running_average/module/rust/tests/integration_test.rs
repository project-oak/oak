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
use running_average_grpc::proto::{
    running_average_client::RunningAverageClient, SubmitSampleRequest,
};

const MODULE_WASM_FILE_NAME: &str = "running_average.wasm";

async fn submit_sample(client: &mut RunningAverageClient<tonic::transport::Channel>, value: u64) {
    let req = SubmitSampleRequest { value };
    let result = client.submit_sample(req).await;
    assert_matches!(result, Ok(_));
}

#[tokio::test(core_threads = 2)]
async fn test_running_average() {
    env_logger::init();

    let runtime = oak_tests::run_single_module_default(MODULE_WASM_FILE_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = RunningAverageClient::with_interceptor(channel, interceptor);

    submit_sample(&mut client, 100).await;
    submit_sample(&mut client, 200).await;

    let result = client.get_average(()).await;
    assert_matches!(result, Ok(_));
    assert_eq!(150, result.unwrap().into_inner().average);

    runtime.stop();
}
