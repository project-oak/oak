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
//! This shows how an Oak Node can aggregate data samples and report aggregated values if there are
//! enough samples to hide individual contributors (enforces k-anonymity).
//!
//! Clients invoke the module by providing data samples that contain a bucket ID
//! and a Sparse Vector - a dictionary with integer keys.

mod data;
mod proto;
#[cfg(test)]
mod tests;

use aggregator_common::ThresholdAggregator;
use data::SparseVector;
use log::{debug, error};
use oak::grpc;
use proto::aggregator::Sample;
use proto::aggregator_grpc::{Aggregator, AggregatorClient, Dispatcher};
use protobuf::well_known_types::Empty;
use std::collections::HashMap;
use std::convert::TryFrom;

/// Currently threshold value is hardcoded.
const SAMPLE_THRESHOLD: u64 = 5;

/// Oak Node that collects and aggregates data.
/// Data is collected in the `aggregators` map where keys are buckets and values are instances of a
/// `ThresholdAggregator`. `Option` is used to keep note of the outdated buckets: once an
/// Aggregator has sent its data to the Backend, it's replaced with `None` and all subsequent client
/// requests corresponding to its bucket are discarded.
pub struct AggregatorNode {
    aggregators: HashMap<String, Option<ThresholdAggregator<SparseVector>>>,
}

impl AggregatorNode {
    fn new() -> Self {
        AggregatorNode {
            aggregators: HashMap::new(),
        }
    }

    /// Submit a data sample (Sparse Vector `svec`) to an Aggregator corresponding to the `bucket`.
    /// If the Aggregator has enough data samples, then report the aggregated value to the backend
    /// server and replace the Aggregator with `None`, so all subsequent client requests
    /// corresponding to the `bucket` will be discarded.
    fn submit(&mut self, bucket: String, svec: &SparseVector) -> Result<(), String> {
        match self.aggregators.get_mut(&bucket) {
            Some(entry) => match *entry {
                Some(ref mut aggregator) => {
                    aggregator.submit(svec);
                    if let Some(aggregated_data) = aggregator.take() {
                        *entry = None;
                        if let Err(err) = self.report(bucket, aggregated_data) {
                            // Backend report errors are not returned to the clients.
                            error!("Backend report error: {:?}", err);
                        }
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

    /// Try to report the aggregated value to the backend server via gRPC.
    /// Return an error if the backend server is not available.
    fn report(&self, bucket: String, svec: SparseVector) -> Result<(), String> {
        debug!(
            "Reporting data to the backend: bucket {}, sparse vector: {:?}",
            bucket, svec
        );

        match oak::grpc::client::Client::new("grpc-client", "").map(AggregatorClient) {
            Some(grpc_client) => {
                let res = grpc_client.submit_sample(Sample {
                    bucket: bucket,
                    data: ::protobuf::SingularPtrField::some(svec.into()),
                    ..Default::default()
                });
                match res {
                    Ok(_) => Ok(()),
                    Err(err) => Err(format!("gRPC send error: {:?}", err)),
                }
            }
            None => Err("Could not create a gRPC client".to_string()),
        }
    }
}

/// A gRPC service implementation for the Aggregator example.
impl Aggregator for AggregatorNode {
    fn submit_sample(&mut self, sample: Sample) -> grpc::Result<Empty> {
        match sample.data.into_option() {
            Some(data) => match SparseVector::try_from(&data) {
                Ok(svec) => {
                    debug!(
                        "Received data: bucket {}, sparse vector: {:?}",
                        sample.bucket, svec
                    );
                    match self.submit(sample.bucket, &svec) {
                        Ok(_) => Ok(Empty::new()),
                        Err(err) => {
                            let err = format!("Submit sample error: {}", err);
                            Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, &err))
                        }
                    }
                }
                Err(err) => {
                    let err = format!("Data deserialization error: {}", err);
                    Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, &err))
                }
            },
            None => {
                let err = "No data specified";
                Err(grpc::build_status(grpc::Code::INVALID_ARGUMENT, &err))
            }
        }
    }
}

oak::entrypoint!(oak_main => {
    oak::logger::init_default();
    let node = AggregatorNode::new();
    Dispatcher::new(node)
});
