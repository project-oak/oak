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
mod application;
mod proto;
#[cfg(test)]
mod tests;

use aggregation::Monoid;
use application::{Application, Serializable};
use itertools::{
    EitherOrBoth::{Both, Left, Right},
    Itertools,
};
use proto::aggregator::Vector;

const SAMPLE_THRESHOLD: u64 = 3;

oak::entrypoint!(oak_main => {
    oak_log::init_default();
    Application::<Vector>::new(SAMPLE_THRESHOLD)
});

impl Monoid for Vector {
    fn identity() -> Self {
        Vector::new()
    }

    /// Adds two non-negative integer vectors elementwise. If vectors have different lengths, then
    /// appends the smallest vector with zeros.
    fn combine(&self, other: &Self) -> Self {
        let mut vector = Vector::new();
        vector.set_items(
            self.items.iter()
                      .zip_longest(other.items.iter())
                      .map(|p| match p {
                          Both(l, r) => *l + *r,
                          Left(l) => *l,
                          Right(r) => *r,
                      })
                      .collect());
        vector
    }
}

impl Serializable<Vector> for Vector {
    fn deserialize(proto: &Vector) -> Self {
        proto.clone()
    }
    fn serialize(&self) -> Vector {
        self.clone()
    }
}

