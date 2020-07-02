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

use assert_matches::assert_matches;
use hello_world_grpc::proto::{hello_world_client::HelloWorldClient, HelloRequest};
use log::info;

const MODULE_WASM_FILE_NAME: &str = "hello_world.wasm";

// Test invoking the SayHello Node service method via the Oak runtime.
#[tokio::test(core_threads = 2)]
async fn test_say_hello() {
    env_logger::init();

    let runtime = oak_tests::run_single_module_default(MODULE_WASM_FILE_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = HelloWorldClient::with_interceptor(channel, interceptor);

    let req = HelloRequest {
        greeting: "world".into(),
    };
    info!("Sending request: {:?}", req);

    let result = client.say_hello(req).await;
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().into_inner().reply);

    runtime.stop();
}
