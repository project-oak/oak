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

//! Aggregator example for Project Oak.
//!
//! This shows how an Oak Node can aggregate data samples and expose the aggregated data only if
//! there are enough samples to hide individual contributors.
//!
//! Clients invoke the module by providing a vector of non-negative numbers, and get back an
//! aggregated vector if an Oak Node has collected more samples than the predefined threshold.

mod aggregation;
mod proto;
mod service;
#[cfg(test)]
mod tests;

use aggregation::{Aggregation, Monoid};
use itertools::{
    EitherOrBoth::{Both, Left, Right},
    Itertools,
};
use service::Serializable;

const SAMPLE_THRESHOLD: u64 = 3;
type Data = Vec<u64>;
type Node = Aggregation<Data>;

oak::entrypoint!(oak_main => {
    oak_log::init_default();
    Node::new(SAMPLE_THRESHOLD)
});

impl Monoid for Data {
    fn identity() -> Self {
        vec![]
    }
    fn combine(&self, other: &Self) -> Self {
        self.iter()
            .zip_longest(other.iter())
            .map(|p| match p {
                Both(l, r) => *l + *r,
                Left(l) => *l,
                Right(r) => *r,
            })
            .collect::<Vec<u64>>()
    }
}

impl Serializable for Data {
    fn deserialize(data: Vec<u64>) -> Self {
        data
    }
    fn serialize(&self) -> Vec<u64> {
        self.to_vec()
    }
}
