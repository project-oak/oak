//
// Copyright 2022 The Project Oak Authors
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

#![cfg(target_arch = "wasm32")]

extern crate wasm_bindgen_test;
use crate::WebClient;
use wasm_bindgen::JsCast;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

const URI: &str = "http://localhost:8080";
const TEST_DATA: [u8; 4] = [1, 2, 3, 4];

#[wasm_bindgen_test]
async fn pass() {
    let client = WebClient::new(URI.to_string()).await.unwrap();
    let js_promise = client.invoke(TEST_DATA.to_vec());
    let js_result = wasm_bindgen_futures::JsFuture::from(js_promise)
        .await
        .unwrap();
    println!("{:?}", js_result);
    let result_as_vec = js_sys::Reflect::get(&js_result, &"body".into())
        .unwrap()
        .dyn_into::<js_sys::Uint8Array>()
        .unwrap()
        .to_vec();
    assert_eq!(result_as_vec, TEST_DATA.to_vec());
}
