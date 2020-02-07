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

use crate::proto::hello_world::{HelloRequest, HelloResponse};
use assert_matches::assert_matches;
use oak::grpc;

const MODULE_CONFIG_NAME: &str = "hello_world";
const LOG_CONFIG_NAME: &str = "log";
const ENTRYPOINT_NAME: &str = "oak_main";

const MODULE_MANIFEST: &str = "Cargo.toml";
const MODULE_WASM_NAME: &str = "hello_world.wasm";

fn build_wasm() -> std::io::Result<Vec<(String, Vec<u8>)>> {
    let mut wasm_file = oak_tests::compile_rust_to_wasm(MODULE_MANIFEST)?;
    wasm_file.push("wasm32-unknown-unknown/debug");
    wasm_file.push(MODULE_WASM_NAME);

    let wasm = std::fs::read(wasm_file)?;

    Ok(vec![(MODULE_CONFIG_NAME.to_owned(), wasm)])
}

// Test invoking the SayHello Node service method via the Oak runtime.
#[test]
fn test_say_hello() {
    simple_logger::init().unwrap();

    let configuration = oak_tests::test_configuration(
        build_wasm().expect("failed to build wasm modules"),
        LOG_CONFIG_NAME,
        MODULE_CONFIG_NAME,
        ENTRYPOINT_NAME,
    );

    let (runtime, entry_channel) = oak_runtime::Runtime::configure_and_run(configuration)
        .expect("Unable to configure runtime with test wasm!");

    let mut req = HelloRequest::new();
    req.set_greeting("world".to_string());
    let result: grpc::Result<HelloResponse> = oak_tests::grpc_request(
        &entry_channel,
        "/oak.examples.hello_world.HelloWorld/SayHello",
        req,
    );
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().reply);

    runtime.stop();
}
