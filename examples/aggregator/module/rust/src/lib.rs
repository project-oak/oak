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

//! Running average example for Project Oak.
//!
//! This shows how an Oak Mode can maintain some internal state across multiple invocations.
//!
//! Clients invoke the module by providing a string representation of a non-negative number
//! expressed in base 10, and get back a string representation of the accumulated average value up
//! to and including the value provided in the request.

mod aggregation;
mod proto;
#[cfg(test)]
mod tests;

use aggregation::{Aggregation, Monoid};
// use log::info;
use oak::grpc;
// use oak::grpc::OakNode;
use proto::aggregator::{GetAggregationResponse, SubmitSampleRequest};
use proto::aggregator_grpc::{dispatch, Aggregator};
use protobuf::well_known_types::Empty;

oak::entrypoint!(oak_main => {
    oak_log::init_default();
    Node {
        aggregation: Aggregation::new(3),
    }
});

impl Monoid for [u64; 10] {
    fn identity() -> Self {
        [0u64; 10]
    }

    fn combine(&self, other: &Self) -> Self {
        let mut array = [0; 10];
        let bytes = &self
            .iter()
            .zip(other.iter())
            .map(|(a, b)| a + b)
            .collect::<Vec<u64>>()[0..10];
        array.copy_from_slice(bytes);
        array
    }

    fn len() -> usize {
        10
    }
}

// #[derive(Default)]
struct Node {
    aggregation: Aggregation<[u64; 10]>,
}

impl grpc::OakNode for Node {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

trait ProtoVec<T: Monoid> {
    fn serialize(data: T) -> Vec<u64>;
    fn deserialize(data: Vec<u64>) -> T;
}

impl ProtoVec<[u64; 10]> for Node {
    fn serialize(data: [u64; 10]) -> Vec<u64> {
        data.to_vec()
    }

    fn deserialize(data: Vec<u64>) -> [u64; 10] {
        let mut array = [0; 10];
        let bytes = &data[0..10];
        array.copy_from_slice(bytes);
        array
    }
}

impl Aggregator for Node {
    fn submit_sample(&mut self, req: SubmitSampleRequest) -> grpc::Result<Empty> {
        if req.values.len() == 10 {
            self.aggregation.add(&Node::deserialize(req.values));
            Ok(Empty::new())
        } else {
            Err(grpc::build_status(
                grpc::Code::INVALID_ARGUMENT,
                "Wrong vector size",
            ))
        }
    }

    fn get_aggregation(&mut self, _req: Empty) -> grpc::Result<GetAggregationResponse> {
        let mut res = GetAggregationResponse::new();
        match self.aggregation.get() {
            Some(values) => {
                res.values = Node::serialize(values);
                Ok(res)
            }
            None => Err(grpc::build_status(
                grpc::Code::UNAVAILABLE,
                "Not enough samples have been aggregated",
            )),
        }
    }
}
