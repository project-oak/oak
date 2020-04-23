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

use crate::{
    data::SparseVector,
    proto::{Sample, SerializedSparseVector},
    SAMPLE_THRESHOLD,
};
use aggregator_common::Monoid;
use assert_matches::assert_matches;
use maplit::hashmap;
use oak::grpc;
use std::{
    collections::HashMap,
    convert::{From, TryFrom},
};

const MODULE_CONFIG_NAME: &str = "aggregator";

fn submit_sample(
    runtime: &oak_runtime::RuntimeProxy,
    entry_handle: oak_abi::Handle,
    bucket: &str,
    indices: Vec<u32>,
    values: Vec<f32>,
) -> grpc::Result<()> {
    let req = Sample {
        bucket: bucket.to_string(),
        data: Some(SerializedSparseVector { indices, values }),
    };
    oak_tests::grpc_request(
        &runtime,
        entry_handle,
        "/oak.examples.aggregator.Aggregator/SubmitSample",
        &req,
    )
}

#[test]
fn test_aggregator() {
    simple_logger::init().unwrap();

    let (runtime, entry_handle) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    for i in 0..SAMPLE_THRESHOLD as u32 {
        assert_matches!(
            submit_sample(
                &runtime,
                entry_handle,
                "test",
                vec![i, i + 1, i + 2],
                vec![10.0, 20.0, 30.0]
            ),
            Ok(_)
        );
    }
    // After sending the `SAMPLE_THRESHOLD` of samples, it's not possible to use the same `bucket`.
    assert_matches!(
        submit_sample(
            &runtime,
            entry_handle,
            "test",
            vec![1, 2, 3],
            vec![10.0, 20.0, 30.0]
        ),
        Err(_)
    );

    runtime.stop_runtime();
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
