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

use aggregator::{data::SparseVector, handler::SAMPLE_THRESHOLD};
use aggregator_common::Monoid;
use aggregator_grpc::proto::{aggregator_client::AggregatorClient, Sample, SerializedSparseVector};
use assert_matches::assert_matches;
use maplit::hashmap;
use oak_abi::{
    label::{confidentiality_label, web_assembly_module_tag},
    proto::oak::application::ConfigMap,
};
use oak_client::interceptors::label::LabelInterceptor;
use oak_sign::get_sha256;
use std::{
    collections::HashMap,
    convert::{From, TryFrom},
};
use tonic::{service::interceptor::InterceptedService, transport::Channel};

const WASM_MODULE_MANIFEST: &str = "../../module/rust/Cargo.toml";
const MODULE_NAME: &str = "app";
const ENTRYPOINT_NAME: &str = "oak_main";
const BACKEND_SERVER_URI: &str = "localhost:8888";

async fn submit_sample(
    client: &mut AggregatorClient<InterceptedService<Channel, LabelInterceptor>>,
    bucket: &str,
    indices: Vec<u32>,
    values: Vec<f32>,
) -> Result<tonic::Response<()>, tonic::Status> {
    let req = Sample {
        bucket: bucket.to_string(),
        data: Some(SerializedSparseVector { indices, values }),
    };
    client.submit_sample(req).await
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_aggregator() {
    let _ = env_logger::builder().is_test(true).try_init();

    let wasm_module =
        oak_tests::compile_rust_wasm(WASM_MODULE_MANIFEST, oak_tests::Profile::Release)
            .expect("Couldn't compile Wasm module");
    let wasm_module_hash = get_sha256(&wasm_module);

    let module_config = format!(
        "grpc_server_listen_address = \"[::]:8080\"\n\
         backend_server_address = \"https://{}\"\n\
         aggregator_module_hash = \"{}\"",
        BACKEND_SERVER_URI,
        hex::encode(&wasm_module_hash)
    );
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_log_nodes: true,
        allow_egress_https_authorities: vec![BACKEND_SERVER_URI.to_string()],
        ..Default::default()
    };

    let config = oak_tests::runtime_config_wasm(
        hashmap! { MODULE_NAME.to_owned() => wasm_module },
        MODULE_NAME,
        ENTRYPOINT_NAME,
        ConfigMap {
            items: hashmap! {
                "config".to_string() => module_config.as_bytes().to_vec()
            },
        },
        permissions,
        oak_runtime::SignatureTable::default(),
    );

    let runtime =
        oak_runtime::configure_and_run(config).expect("Unable to configure runtime with test wasm");

    let hash_label = confidentiality_label(web_assembly_module_tag(&wasm_module_hash));
    let (channel, interceptor) = oak_tests::channel_and_interceptor(&hash_label).await;
    let mut client = AggregatorClient::with_interceptor(channel, interceptor);

    for i in 0..SAMPLE_THRESHOLD as u32 {
        assert_matches!(
            submit_sample(
                &mut client,
                "test",
                vec![i, i + 1, i + 2],
                vec![10.0, 20.0, 30.0]
            )
            .await,
            Ok(_)
        );
    }
    // After sending the `SAMPLE_THRESHOLD` of samples, it's not possible to use the same `bucket`.
    assert_matches!(
        submit_sample(&mut client, "test", vec![1, 2, 3], vec![10.0, 20.0, 30.0]).await,
        Err(_)
    );

    runtime.stop();
}

#[test]
fn test_combine() {
    type Map = HashMap<u32, f32>;
    struct Test {
        in_0: Map,
        in_1: Map,
        out: Map,
    }
    let tests = vec![
        Test {
            in_0: hashmap! {},
            in_1: hashmap! { 1 => 10.0 },
            out: hashmap! { 1 => 10.0 },
        },
        Test {
            in_0: hashmap! {1 => 10.0},
            in_1: hashmap! {2 => 20.0},
            out: hashmap! {1 => 10.0, 2 => 20.0},
        },
        Test {
            in_0: hashmap! {1 => 10.0},
            in_1: hashmap! {2 => 20.0, 3 => 30.0},
            out: hashmap! {1 => 10.0, 2 => 20.0, 3 => 30.0},
        },
        Test {
            in_0: hashmap! {1 => 10.0, 2 => 20.0, 3 => 30.0},
            in_1: hashmap! {2 => 20.0, 3 => 30.0},
            out: hashmap! {1 => 10.0, 2 => 40.0, 3 => 60.0},
        },
    ];
    for test in tests {
        assert_eq!(
            SparseVector::new(test.in_0).combine(&SparseVector::new(test.in_1)),
            SparseVector::new(test.out)
        );
    }
}

#[test]
fn test_serialize() {
    // Use the module-internal version of the protobuf-derived struct.
    // TODO(#1093): unify the two versions
    use aggregator::proto::oak::examples::aggregator::SerializedSparseVector;
    assert_eq!(
        SerializedSparseVector::from(SparseVector::new(hashmap! {1 => 10.0})),
        SerializedSparseVector {
            indices: vec![1],
            values: vec![10.0],
        }
    );
    assert_eq!(
        SparseVector::try_from(&SerializedSparseVector {
            indices: vec![1, 2],
            values: vec![10.0, 20.0],
        }),
        Ok(SparseVector::new(hashmap! {1 => 10.0, 2 => 20.0}))
    );
    assert_matches!(
        SparseVector::try_from(&SerializedSparseVector {
            indices: vec![1, 1], // Duplicated indices are not allowed.
            values: vec![10.0, 20.0],
        }),
        Err(_)
    );
    assert_matches!(
        SparseVector::try_from(&SerializedSparseVector {
            indices: vec![1],
            values: vec![10.0, 20.0],
        }),
        Err(_)
    );
    assert_matches!(
        SparseVector::try_from(&SerializedSparseVector {
            indices: vec![1, 2],
            values: vec![10.0],
        }),
        Err(_)
    );
}
