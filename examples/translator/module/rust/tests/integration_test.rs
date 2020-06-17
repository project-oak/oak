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
use log::info;
use translator_grpc::proto::{translator_client::TranslatorClient, TranslateRequest};

const MODULE_CONFIG_NAME: &str = "translator";

#[tokio::test(core_threads = 2)]
async fn test_translate() {
    env_logger::init();

    let runtime = oak_tests::run_single_module(MODULE_CONFIG_NAME, "grpc_oak_main")
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = TranslatorClient::with_interceptor(channel, interceptor);

    let req = TranslateRequest {
        text: "WORLDS".into(),
        from_lang: "en".into(),
        to_lang: "it".into(),
    };
    info!("Sending request: {:?}", req);

    let result = client.translate(req).await;
    assert_matches!(result, Ok(_));
    assert_eq!("MONDI", result.unwrap().into_inner().translated_text);

    runtime.stop();
}
