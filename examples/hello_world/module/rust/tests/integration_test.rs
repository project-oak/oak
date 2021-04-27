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
use hello_world_grpc::proto::{hello_world_client::HelloWorldClient, HelloRequest, HelloResponse};
use log::info;
use maplit::hashmap;
use oak::proto::oak::application::ConfigMap;
use tokio_stream::StreamExt;

const MAIN_MODULE_NAME: &str = "app";
const MAIN_ENTRYPOINT_NAME: &str = "oak_main";
const MAIN_MODULE_MANIFEST: &str = "../../module/rust/Cargo.toml";

const TRANSLATOR_MODULE_NAME: &str = "translator";
const TRANSLATOR_MODULE_MANIFEST: &str = "../../../translator/module/rust/Cargo.toml";

// Test invoking the SayHello Node service method via the Oak runtime.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_say_hello() {
    let _ = env_logger::builder().is_test(true).try_init();
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_log_nodes: true,
        ..Default::default()
    };
    let runtime_config = oak_tests::runtime_config_wasm(
        hashmap! {
            MAIN_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(MAIN_MODULE_MANIFEST, oak_tests::Profile::Release).expect("Couldn't compile main module"),
            TRANSLATOR_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(TRANSLATOR_MODULE_MANIFEST, oak_tests::Profile::Release).expect("Couldn't compile translator module"),
        },
        MAIN_MODULE_NAME,
        MAIN_ENTRYPOINT_NAME,
        ConfigMap::default(),
        permissions,
        oak_runtime::SignatureTable::default(),
    );
    let runtime = oak_runtime::configure_and_run(runtime_config)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
    let mut client = HelloWorldClient::with_interceptor(channel, interceptor);

    {
        let req = HelloRequest {
            greeting: "world".into(),
        };
        info!("Sending request: {:?}", req);
        let result = client.say_hello(req.clone()).await;
        assert_matches!(result, Ok(_));
        assert_eq!("HELLO world!", result.unwrap().into_inner().reply);
    }
    {
        let req = HelloRequest {
            greeting: "WORLDS".into(),
        };
        info!("Sending request: {:?}", req);
        let result = client.lots_of_replies(req).await;
        assert_matches!(result, Ok(_));
        // Make sure that the translated response was received.
        assert_eq!(
            vec![
                HelloResponse {
                    reply: "HELLO WORLDS!".to_string()
                },
                HelloResponse {
                    reply: "BONJOUR MONDES!".to_string()
                },
                HelloResponse {
                    reply: "HELLO AGAIN WORLDS!".to_string()
                },
            ],
            result
                .unwrap()
                .into_inner()
                .collect::<Vec<Result<HelloResponse, tonic::Status>>>()
                .await
                .into_iter()
                .filter_map(Result::ok)
                .collect::<Vec<HelloResponse>>()
        );
    }

    runtime.stop();
}
