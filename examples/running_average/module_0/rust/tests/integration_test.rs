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

use anyhow::Context;
use assert_matches::assert_matches;
use maplit::hashmap;
use oak_abi::proto::oak::application::ConfigMap;
use oak_sign::{read_pem_file, KeyPair, SignatureBundle};
use running_average_grpc::proto::{
    running_average_client::RunningAverageClient, SubmitSampleRequest,
};
use std::collections::HashMap;

// Base64 encoded Ed25519 private key corresponding to Wasm module signature.
const PRIVATE_KEY_FILE: &str = "../../../keys/ed25519/test.key";

const MAIN_MODULE_FILE_NAME: &str = "running_average.wasm";
const HANDLER_MODULE_FILE_NAME: &str = "running_average_handler.wasm";

const MAIN_MODULE_MANIFEST: &str = "../../module_0/rust/Cargo.toml";
const HANDLER_MODULE_MANIFEST: &str = "../../module_1/rust/Cargo.toml";

const MAIN_MODULE_NAME: &str = "app";
const HANDLER_MODULE_NAME: &str = "handler";
const ENTRYPOINT_NAME: &str = "oak_main";

fn build_wasm() -> anyhow::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        MAIN_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(MAIN_MODULE_MANIFEST, MAIN_MODULE_FILE_NAME, oak_tests::Profile::Debug).context("Couldn't compile frontend module")?,
        HANDLER_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(HANDLER_MODULE_MANIFEST, HANDLER_MODULE_FILE_NAME, oak_tests::Profile::Debug).context("Couldn't compile backend module")?,
    })
}

fn sign(input: &[u8]) -> anyhow::Result<SignatureBundle> {
    let key_file = read_pem_file(PRIVATE_KEY_FILE)?;
    let key_pair = KeyPair::parse(&key_file)?;
    SignatureBundle::create(input, &key_pair)
}

async fn submit_sample(client: &mut RunningAverageClient<tonic::transport::Channel>, value: u64) {
    let req = SubmitSampleRequest { value };
    let result = client.submit_sample(req).await;
    assert_matches!(result, Ok(_));
}

#[tokio::test(core_threads = 2)]
async fn test_running_average() {
    let _ = env_logger::builder().is_test(true).try_init();

    let wasm_modules = build_wasm().expect("Couldn't compile Wasm modules");
    let signature =
        sign(&wasm_modules.get(HANDLER_MODULE_NAME).unwrap()).expect("Couldn't sign Wasm module");
    let config = oak_tests::runtime_config_wasm(
        wasm_modules,
        MAIN_MODULE_NAME,
        ENTRYPOINT_NAME,
        ConfigMap::default(),
        oak_runtime::SignatureTable {
            values: hashmap! {
                hex::encode(&signature.hash) => vec![signature.clone()]
            },
        },
    );
    let runtime =
        oak_runtime::configure_and_run(config).expect("Unable to configure runtime with test wasm");

    let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
    let mut client = RunningAverageClient::with_interceptor(channel, interceptor);

    submit_sample(&mut client, 100).await;
    submit_sample(&mut client, 200).await;

    let result = client.get_average(()).await;
    assert_matches!(result, Ok(_));
    assert_eq!(150, result.unwrap().into_inner().average);

    runtime.stop();
}
