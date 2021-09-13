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
    proto::oak::examples::aggregator::{
        Aggregator, AggregatorClient, AggregatorDispatcher, HandlerInit, Sample,
    },
};
use aggregator_common::{AggregatorResult, ThresholdAggregator};
use log::{debug, error};
use oak::{grpc, io::Sender};
use std::{collections::HashMap, convert::TryFrom};

/// Currently threshold value is hardcoded.
pub const SAMPLE_THRESHOLD: u64 = 5;

/// Oak Node that collects and aggregates data.
/// Data is collected in the `aggregators` map where keys are buckets and values are instances of a
/// `ThresholdAggregator`. `Option` is used to keep note of the outdated buckets: once an
/// Aggregator has sent its data to the Backend, it's replaced with `None` and all subsequent client
/// requests corresponding to its bucket are discarded.
pub struct Handler {
    backend_client: AggregatorClient,
    aggregators: HashMap<String, ThresholdAggregator<SparseVector>>,
}

impl Handler {
    fn new(invocation_sender: Sender<grpc::Invocation>) -> Self {
        Self {
            backend_client: AggregatorClient(invocation_sender),
            aggregators: HashMap::new(),
        }
    }

    /// Submit a data sample (Sparse Vector `svec`) to an Aggregator corresponding to the `bucket`.
    /// If the Aggregator has enough data samples, then report the aggregated value to the backend
    /// server and replace the Aggregator with `None`, so all subsequent client requests
    /// corresponding to the `bucket` will be discarded.
    fn submit(&mut self, bucket: String, svec: &SparseVector) -> Result<(), String> {
        let aggregator = self
            .aggregators
            .entry(bucket.clone())
            .or_insert_with(|| ThresholdAggregator::<SparseVector>::new(SAMPLE_THRESHOLD));
        match aggregator.submit(svec) {
            AggregatorResult::BelowThreshold => Ok(()),
            AggregatorResult::Exhausted => Err(format!("Exhausted bucket: {}", bucket)),
            AggregatorResult::AggregatedValue(aggregated_data) => {
                let aggregated_data = aggregated_data.clone();
                if let Err(err) = self.report(bucket, aggregated_data) {
                    // Backend report errors are not returned to the clients.
                    error!("Backend report error: {:?}", err);
                }
                Ok(())
            }
        }
    }

    /// Try to report the aggregated value to the backend server via gRPC.
    /// Return an error if the backend server is not available.
    fn report(&self, bucket: String, svec: SparseVector) -> Result<(), String> {
        debug!(
            "Reporting data to the backend: bucket {}, sparse vector: {:?}",
            bucket, svec
        );
        let result = self.backend_client.submit_sample(Sample {
            bucket,
            data: Some(svec.into()),
        });
        match result {
            Ok(response) => {
                debug!("Data report response: {:?}", response);
                Ok(())
            }
            Err(err) => Err(format!("gRPC send error: {:?}", err)),
        }
    }
}

/// A gRPC service implementation for the Aggregator example.
impl Aggregator for Handler {
    fn submit_sample(&mut self, sample: Sample) -> grpc::Result<()> {
        match sample.data {
            Some(data) => match SparseVector::try_from(&data) {
                Ok(svec) => {
                    debug!(
                        "Received data: bucket {}, sparse vector: {:?}",
                        sample.bucket, svec
                    );
                    match self.submit(sample.bucket, &svec) {
                        Ok(_) => Ok(()),
                        Err(err) => {
                            let err = format!("Submit sample error: {}", err);
                            Err(grpc::build_status(grpc::Code::InvalidArgument, &err))
                        }
                    }
                }
                Err(err) => {
                    let err = format!("Data deserialization error: {}", err);
                    Err(grpc::build_status(grpc::Code::InvalidArgument, &err))
                }
            },
            None => {
                let err = "No data specified";
                Err(grpc::build_status(grpc::Code::InvalidArgument, err))
            }
        }
    }
}

impl oak::WithInit for Handler {
    type Init = HandlerInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        let grpc_client_invocation_sender = init
            .grpc_client_invocation_sender
            .expect("Couldn't receive gRPC invocation sender")
            .sender
            .expect("Empty gRPC invocation sender");

        Self::new(grpc_client_invocation_sender)
    }
}

oak::impl_dispatcher!(impl Handler : AggregatorDispatcher);

oak::entrypoint_command_handler_init!(handler => Handler);
