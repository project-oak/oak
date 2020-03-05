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
//! Clients invoke the module by providing a vector of non-negative numbers and get back an
//! aggregated vector if an Oak Node has collected more samples than the predefined threshold.

mod proto;
#[cfg(test)]
mod tests;

use aggregator_common::{Monoid, ThresholdAggregator};
use log::info;
use oak::grpc;
use proto::aggregator_test::Vector;
use proto::aggregator_test_grpc::{Aggregator, Dispatcher};
use protobuf::well_known_types::Empty;

const SAMPLE_THRESHOLD: u64 = 3;

oak::entrypoint!(oak_main => {
    oak::logger::init_default();
    let node = AggregatorNode {
        aggregator: ThresholdAggregator::<Vector>::new(SAMPLE_THRESHOLD),
    };
    Dispatcher::new(node)
});

impl Monoid for Vector {
    fn identity() -> Self {
        Vector::new()
    }

    /// Adds two non-negative integer vectors elementwise. If vectors have different lengths, then
    /// pads the smallest vector with zeros.
    fn combine(&self, other: &Self) -> Self {
        use itertools::EitherOrBoth::*;
        use itertools::Itertools;

        Vector {
            items: self
                .items
                .iter()
                .zip_longest(other.items.iter())
                .map(|p| match p {
                    Both(l, r) => *l + *r,
                    Left(l) => *l,
                    Right(r) => *r,
                })
                .collect(),
            ..Default::default()
        }
    }
}

/// Oak Node that collects aggregated data.
pub struct AggregatorNode {
    aggregator: ThresholdAggregator<Vector>,
}

/// A gRPC service implementation for the Aggregator example.
impl Aggregator for AggregatorNode {
    fn submit_sample(&mut self, sample: Vector) -> grpc::Result<Empty> {
        info!("Submitted sample: {:?}", sample);
        self.aggregator.submit(&sample);
        Ok(Empty::new())
    }

    fn get_current_value(&mut self, _: Empty) -> grpc::Result<Vector> {
        let value = self.aggregator.get().cloned().ok_or_else(|| {
            grpc::build_status(
                grpc::Code::FAILED_PRECONDITION,
                "Not enough samples have been aggregated",
            )
        });
        info!("Returning value: {:?}", value);
        value
    }
}
