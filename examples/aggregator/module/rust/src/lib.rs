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

mod data;
mod proto;
#[cfg(test)]
mod tests;

use aggregator_common::ThresholdAggregator;
use data::SparseVector;
use log::{debug, error};
use oak::grpc;
use proto::aggregator::Sample;
use proto::aggregator_grpc::{Aggregator, Dispatcher};
use protobuf::well_known_types::Empty;
use std::collections::HashMap;
use std::convert::{From, TryFrom};

/// Currently threshold value is hardcoded.
const SAMPLE_THRESHOLD: u64 = 5;

type ThresholdAggregatorMap = HashMap<String, ThresholdAggregator<SparseVector>>;

/// Oak Node that collects aggregated data.
pub struct AggregatorNode {
    aggregators: ThresholdAggregatorMap,
}

impl AggregatorNode {
    fn submit_sparse_vector(&mut self, bucket: &String, svec: &SparseVector) {
        let aggregator = self.aggregators
            .entry(bucket.to_string())
            .and_modify(|aggregator| {
                aggregator.submit(svec);
            })
            .or_insert({
                let mut aggregator = ThresholdAggregator::<SparseVector>::new(SAMPLE_THRESHOLD);
                aggregator.submit(svec);
                aggregator
            });
        // TODO: Use Option for ThresholdAggregator
        if let Some(aggregated_data) = aggregator.take() {
            self.send_aggregated_data(&bucket, aggregated_data);
        }
    }

    fn send_aggregated_data(&mut self, bucket: &String, svec: SparseVector) {
        debug!(
            "Sending aggregated data: bucket {}, sparse vector: {:?}",
            bucket, svec
        );
    }
}

/// A gRPC service implementation for the Aggregator example.
impl Aggregator for AggregatorNode {
    fn submit_sample(&mut self, sample: Sample) -> grpc::Result<Empty> {
        match sample.data.into_option() {
            Some(data) => {
                match SparseVector::try_from(data) {
                    Ok(svec) => {
                        debug!(
                            "Submitted data: bucket {}, sparse vector: {:?}",
                            sample.bucket, svec
                        );
                        self.submit_sparse_vector(&sample.bucket, &svec);
                        Ok(Empty::new())
                    }
                    Err(err) => {
                        error!("Data deserialization error: {}", err);
                        Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, err))
                    }
                }
            },
            None => {
                let err = "No data specified";
                error!("{}", err);
                Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, err))
            }
        }
    }
}

oak::entrypoint!(oak_main => {
    oak_log::init_default();
    let node = AggregatorNode {
        aggregators: ThresholdAggregatorMap::new(),
    };
    Dispatcher::new(node)
});
