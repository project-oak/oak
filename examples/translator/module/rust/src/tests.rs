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
use oak::grpc;
use translator_common::proto::{TranslateRequest, TranslateResponse};

const MODULE_CONFIG_NAME: &str = "translator";

#[test]
fn test_translate() {
    simple_logger::init().unwrap();

    let (runtime, entry_handle) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let req = TranslateRequest {
        text: "WORLDS".into(),
        from_lang: "en".into(),
        to_lang: "it".into(),
    };
    let result: grpc::Result<TranslateResponse> = oak_tests::grpc_request(
        &runtime,
        entry_handle,
        "/oak.examples.translator.Translator/Translate",
        &req,
    );
    assert_matches!(result, Ok(_));
    assert_eq!("MONDI", result.unwrap().translated_text);

    runtime.stop_runtime();
}
