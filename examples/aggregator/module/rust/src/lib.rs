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
use proto::aggregator::{Sample, SerializedSparseVector};
use proto::aggregator_grpc::{Aggregator, AggregatorClient, Dispatcher};
use protobuf::well_known_types::Empty;
use std::collections::HashMap;
use std::convert::{From, TryFrom};

/// Currently threshold value is hardcoded.
const SAMPLE_THRESHOLD: u64 = 2;

type ThresholdAggregatorMap = HashMap<String, Option<ThresholdAggregator<SparseVector>>>;

/// Oak Node that collects aggregated data.
pub struct AggregatorNode {
    aggregators: ThresholdAggregatorMap,
    grpc_client: AggregatorClient,
}

impl AggregatorNode {
    fn new() -> Result<Self, &'static str> {
        match oak::grpc::client::Client::new("grpc-client", "ignored").map(AggregatorClient) {
            Some(grpc_client) => Ok(AggregatorNode {
                aggregators: ThresholdAggregatorMap::new(),
                grpc_client: grpc_client,
            }),
            None => Err("Could not create a gRPC client"),
        }
    }

    fn submit_sparse_vector(&mut self, bucket: String, svec: &SparseVector) -> Result<(), String> {
        match self.aggregators.get_mut(&bucket) {
            Some(entry) => match *entry {
                Some(ref mut aggregator) => {
                    aggregator.submit(svec);
                    if let Some(aggregated_data) = aggregator.take() {
                        *entry = None;
                        self.send_aggregated_data(bucket, aggregated_data);
                    }
                }
                None => Err(format!("Outdated bucket: {}", bucket))?,
            },
            None => {
                let mut aggregator = ThresholdAggregator::<SparseVector>::new(SAMPLE_THRESHOLD);
                aggregator.submit(svec);
                self.aggregators.insert(bucket, Some(aggregator));
            }
        }
        Ok(())
    }

    fn send_aggregated_data(&self, bucket: String, svec: SparseVector) {
        debug!(
            "Sending aggregated data: bucket {}, sparse vector: {:?}",
            bucket, svec
        );
        // Currently the Node panics if it couldn't send a gRPC request.
        self.grpc_client
            .submit_sample(Sample {
                bucket: bucket,
                data: ::protobuf::SingularPtrField::some(SerializedSparseVector::from(svec)),
                ..Default::default()
            })
            .unwrap();
    }
}

/// A gRPC service implementation for the Aggregator example.
impl Aggregator for AggregatorNode {
    fn submit_sample(&mut self, sample: Sample) -> grpc::Result<Empty> {
        match sample.data.into_option() {
            Some(data) => match SparseVector::try_from(data) {
                Ok(svec) => {
                    debug!(
                        "Submitted data: bucket {}, sparse vector: {:?}",
                        sample.bucket, svec
                    );
                    match self.submit_sparse_vector(sample.bucket, &svec) {
                        Ok(_) => Ok(Empty::new()),
                        Err(err) => {
                            error!("Sparse Vector submission error: {}", err);
                            Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, &err))
                        }
                    }
                }
                Err(err) => {
                    error!("Data deserialization error: {}", err);
                    Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, &err))
                }
            },
            None => {
                let err = "No data specified";
                error!("{}", err);
                Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, &err))
            }
        }
    }
}

oak::entrypoint!(oak_main => {
    oak::logger::init_default();
    // Currently the Node panics if it couldn't create a gRPC client.
    let node = AggregatorNode::new().unwrap();
    Dispatcher::new(node)
});
