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
use oak_abi::{
    label::{confidentiality_label, web_assembly_module_signature_tag},
    proto::oak::application::ConfigMap,
};
use oak_sign::{read_pem_file, KeyPair, SignatureBundle};
use private_set_intersection_grpc::proto::{
    private_set_intersection_client::PrivateSetIntersectionClient, GetIntersectionRequest,
    SubmitSetRequest,
};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};

// Base64 encoded Ed25519 private key corresponding to Wasm module signature.
const PRIVATE_KEY_FILE: &str = "../../../keys/ed25519/test.key";

const MAIN_MODULE_MANIFEST: &str = "../../main_module/rust/Cargo.toml";
const HANDLER_MODULE_MANIFEST: &str = "../../handler_module/rust/Cargo.toml";

const MAIN_MODULE_NAME: &str = "app";
const HANDLER_MODULE_NAME: &str = "handler";
const ENTRYPOINT_NAME: &str = "oak_main";

const TEST_SET_ID: &str = "test";

fn build_wasm() -> anyhow::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        MAIN_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(MAIN_MODULE_MANIFEST, oak_tests::Profile::Release).context("Couldn't compile main module")?,
        HANDLER_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(HANDLER_MODULE_MANIFEST, oak_tests::Profile::Release).context("Couldn't compile handler module")?,
    })
}

fn sign(input: &[u8]) -> anyhow::Result<SignatureBundle> {
    let key_file = read_pem_file(PRIVATE_KEY_FILE)?;
    let key_pair = KeyPair::parse(&key_file)?;
    SignatureBundle::create(input, &key_pair)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_set_intersection() {
    let _ = env_logger::builder().is_test(true).try_init();

    let wasm_modules = build_wasm().expect("Couldn't compile Wasm modules");
    let signature =
        sign(wasm_modules.get(HANDLER_MODULE_NAME).unwrap()).expect("Couldn't sign Wasm module");
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_log_nodes: true,
        ..Default::default()
    };
    let config = oak_tests::runtime_config_wasm(
        wasm_modules,
        MAIN_MODULE_NAME,
        ENTRYPOINT_NAME,
        ConfigMap::default(),
        permissions,
        oak_runtime::SignatureTable {
            values: hashmap! {
                hex::encode(&signature.hash) => vec![signature.clone()]
            },
        },
    );
    let runtime =
        oak_runtime::configure_and_run(config).expect("Unable to configure runtime with test wasm");

    let public_key_label =
        confidentiality_label(web_assembly_module_signature_tag(&signature.public_key_der));
    let (channel, interceptor) = oak_tests::channel_and_interceptor(&public_key_label).await;
    let mut client = PrivateSetIntersectionClient::with_interceptor(channel, interceptor);

    let req = SubmitSetRequest {
        set_id: TEST_SET_ID.to_string(),
        values: vec!["a".to_string(), "b".to_string(), "c".to_string()],
    };
    let result = client.submit_set(req).await;
    assert_matches!(result, Ok(_));

    let req = SubmitSetRequest {
        set_id: TEST_SET_ID.to_string(),
        values: vec!["b".to_string(), "c".to_string(), "d".to_string()],
    };
    let result = client.submit_set(req).await;
    assert_matches!(result, Ok(_));

    // Send more sets than threshold.
    let req = SubmitSetRequest {
        set_id: TEST_SET_ID.to_string(),
        values: vec!["c".to_string()],
    };
    let result = client.submit_set(req).await;
    assert_matches!(result, Err(_));

    let result = client
        .get_intersection(GetIntersectionRequest {
            set_id: TEST_SET_ID.to_string(),
        })
        .await;
    assert_matches!(result, Ok(_));
    let got = HashSet::<String>::from_iter(result.unwrap().into_inner().values.to_vec());
    let want: HashSet<String> = ["b".to_string(), "c".to_string()].iter().cloned().collect();
    assert_eq!(got, want);

    // Send a new set after the intersection was requested.
    let req = SubmitSetRequest {
        set_id: TEST_SET_ID.to_string(),
        values: vec!["c".to_string()],
    };
    let result = client.submit_set(req).await;
    assert_matches!(result, Err(_));

    runtime.stop();
}
