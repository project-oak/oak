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

use prometheus::{
    opts, register_histogram, register_int_counter, register_int_gauge, Histogram, IntCounter,
    IntGauge,
};

pub mod server;

/// Struct that collects all the metrics in one place
pub struct Metrics {
    pub grpc_request_duration: Histogram,
    pub grpc_requests_total: IntCounter,
    pub grpc_response_size: Histogram,
    pub runtime_nodes_count: IntGauge,
}

// TODO(#899): For testability implement a trait with methods for updating the metrics.
// TODO(#899): Instead of using a global Registry, the Runtime should instantiate and manage the
// Registry
impl Metrics {
    fn new() -> Self {
        Self {
            grpc_request_duration: register_histogram!(
                "grpc_request_duration_seconds",
                "The gRPC request latencies in seconds."
            )
            .expect("Creating grpc_request_duration_seconds metric failed."),

            grpc_requests_total: register_int_counter!(opts!(
                "grpc_requests_total",
                "Total number of gRPC requests received."
            ))
            .expect("Creating grpc_requests_total metric failed."),

            grpc_response_size: register_histogram!(
                "grpc_response_size_bytes",
                "The gRPC response sizes in bytes."
            )
            .expect("Creating grpc_response_size_bytes metric failed."),

            runtime_nodes_count: register_int_gauge!(opts!(
                "runtime_nodes_count",
                "Number of nodes in the runtime."
            ))
            .expect("Creating runtime_nodes_count metric failed."),
        }
    }
}

lazy_static::lazy_static! {
    pub static ref METRICS: Metrics = Metrics::new();
}
