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

use aggregator::{data::SparseVector, SAMPLE_THRESHOLD};
use aggregator_common::Monoid;
use aggregator_grpc::proto::{aggregator_client::AggregatorClient, Sample, SerializedSparseVector};
use assert_matches::assert_matches;
use maplit::hashmap;
use std::{
    collections::HashMap,
    convert::{From, TryFrom},
};

const MODULE_WASM_FILE_NAME: &str = "aggregator.wasm";

async fn submit_sample(
    client: &mut AggregatorClient<tonic::transport::Channel>,
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

#[tokio::test(core_threads = 2)]
async fn test_aggregator() {
    env_logger::init();

    let runtime = oak_tests::run_single_module_default(MODULE_WASM_FILE_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
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
    use aggregator::proto::SerializedSparseVector;
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
