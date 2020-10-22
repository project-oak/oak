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

pub mod proto {
    pub mod oak {
        pub use oak::proto::oak::invocation;
        pub mod examples {
            pub mod aggregator {
                include!(concat!(env!("OUT_DIR"), "/oak.examples.aggregator.rs"));
                include!(concat!(env!("OUT_DIR"), "/oak.examples.aggregator_init.rs"));
            }
        }
    }
}

pub mod data;

use aggregator_common::ThresholdAggregator;
use data::SparseVector;
use log::{debug, error, info};
use oak::{
    grpc,
    io::{Receiver, ReceiverExt, SenderExt},
    proto::oak::invocation::{GrpcInvocation, GrpcInvocationReceiver, GrpcInvocationSender},
};
use oak_abi::proto::oak::application::ConfigMap;
use proto::oak::examples::aggregator::{
    Aggregator, AggregatorClient, AggregatorDispatcher, AggregatorInit, Sample,
};
use std::{collections::HashMap, convert::TryFrom};

/// Currently threshold value is hardcoded.
pub const SAMPLE_THRESHOLD: u64 = 5;

/// Oak Node that collects and aggregates data.
/// Data is collected in the `aggregators` map where keys are buckets and values are instances of a
/// `ThresholdAggregator`. `Option` is used to keep note of the outdated buckets: once an
/// Aggregator has sent its data to the Backend, it's replaced with `None` and all subsequent client
/// requests corresponding to its bucket are discarded.
pub struct AggregatorNode {
    aggregator_client: AggregatorClient,
    aggregators: HashMap<String, Option<ThresholdAggregator<SparseVector>>>,
}

impl AggregatorNode {
    fn new(aggregator_client: oak::grpc::client::Client) -> Self {
        AggregatorNode {
            aggregator_client: AggregatorClient(aggregator_client),
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
                None => return Err(format!("Outdated bucket: {}", bucket)),
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
        let result = self.aggregator_client.submit_sample(Sample {
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
impl Aggregator for AggregatorNode {
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
                Err(grpc::build_status(grpc::Code::InvalidArgument, &err))
            }
        }
    }
}

oak::entrypoint!(aggregator<AggregatorInit> => |init_receiver: Receiver<AggregatorInit>| {
    oak::logger::init_default();

    // Receive the initialization message.
    let init_message: AggregatorInit = init_receiver.receive().expect("Couldn't receive init message");
    let grpc_server_invocation_receiver = init_message
        .grpc_server_invocation_receiver
        .expect("Couldn't receive gRPC invocation receiver")
        .receiver
        .expect("Empty gRPC invocation sender");
    let grpc_client_invocation_sender = init_message
        .grpc_client_invocation_sender
        .expect("Couldn't receive gRPC invocation sender")
        .sender
        .expect("Empty gRPC invocation sender");

    // Run event loop and handle incoming invocations.
    let node = AggregatorNode::new(
        oak::grpc::client::Client {
            invocation_sender: grpc_client_invocation_sender
        }
    );
    let dispatcher = AggregatorDispatcher::new(node);
    oak::run_command_loop(dispatcher, grpc_server_invocation_receiver);
});

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub grpc_server_listen_address: String,
}

/// Create initialization message for Aggregator Node.
fn create_init_message(
    receiver: &oak::io::Receiver<GrpcInvocation>,
    sender: &oak::io::Sender<GrpcInvocation>,
) -> AggregatorInit {
    AggregatorInit {
        grpc_server_invocation_receiver: Some(GrpcInvocationReceiver {
            receiver: Some(receiver.clone()),
        }),
        grpc_client_invocation_sender: Some(GrpcInvocationSender {
            sender: Some(sender.clone()),
        }),
    }
}

oak::entrypoint!(oak_main<ConfigMap> => |receiver: Receiver<ConfigMap>| {
    oak::logger::init_default();

    // Parse config.
    let config_map = receiver.receive().expect("Couldn't read config map");
    let config: Config = toml::from_slice(&config_map.items.get("config").expect("Couldn't find config")).expect("Couldn't parse TOML config file");
    info!("Parsed config: {:?}", config);
    let grpc_server_channel =
        oak::grpc::server::init(&config.grpc_server_listen_address).expect("Couldn't create gRPC server pseudo-Node");

    // Create an Aggregator Node.
    let (init_sender, init_receiver) = oak::io::channel_create::<AggregatorInit>()
        .expect("Couldn't create initialization channel");
    oak::node_create(&oak::node_config::wasm("app", "aggregator"), init_receiver.handle)
        .expect("Couldn't create gRPC worker node");
    oak::channel_close(init_receiver.handle.handle).expect("Couldn't close receiver channel");

    // Create a gRPC client Node with a less restrictive label than the current Node.
    // In particular, the confidentiality component of the current Node label includes the
    // "aggregator" WebAssembly hash, which is declassified as part of the gRPC client
    // Node creation. This is only allowed if the current Node actually has the
    // appropriate capability (i.e. the correct WebAssembly module hash) as specified by
    // the label component being removed, as set by the client.
    // TODO(#814): Uncomment and use correct confidentiality labels.
    // let label = Label {
    //     confidentiality_tags: vec![Tag {
    //         tag: Some(tag::Tag::TlsEndpointTag(TlsEndpointTag {
    //             certificate_subject_alternative_name: "google.com".to_string(),
    //         })),
    //     }],
    //     integrity_tags: vec![],
    // };
    let grpc_client = oak::grpc::client::Client::new(
        &oak::node_config::grpc_client("https://localhost:8888"),
    )
    .expect("Couldn't create gRPC client");

    // Send the initialization message to Aggregator Node containing a gRPC server invocation
    // receiver and a gRPC client invocation sender.
    debug!("Sending the initialization message to handler Node");
    let (invocation_sender, invocation_receiver) = oak::io::channel_create::<grpc::Invocation>()
        .expect("Couldn't create gRPC invocation channel");
    let init_message = create_init_message(&invocation_receiver, &grpc_client.invocation_sender);
    init_sender.send(&init_message).expect("Couldn't send the initialization message to Aggregator Node");

    // Route gRPC invocations to Aggregator Node.
    while let Ok(invocation) = grpc_server_channel.receive() {
        invocation_sender
            .send(&invocation)
            .expect("Couldn't send invocation to worker node");
    }
});
