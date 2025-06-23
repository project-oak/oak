//
// Copyright 2025 The Project Oak Authors
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

use std::sync::Arc;

use oak_containers_agent::metrics::OakObserver;
use opentelemetry::{
    metrics::{Counter, Histogram},
    KeyValue,
};

pub struct Metrics {
    // Total number of RPCs received by the private memory server.
    pub rpc_count: Counter<u64>,
    // Number of RPCs that failed.
    pub rpc_failure_count: Counter<u64>,
    // Latency of each RPC.
    pub rpc_latency: Histogram<u64>,
}

impl Metrics {
    pub fn new(observer: &mut OakObserver) -> Self {
        let rpc_count = observer
            .meter
            .u64_counter("rpc_count")
            .with_description("Total number of RPCs received by the private memory server.")
            .init();
        let rpc_failure_count = observer
            .meter
            .u64_counter("rpc_failure_count")
            .with_description("Number of RPCs that failed.")
            .init();
        let rpc_latency = observer
            .meter
            .u64_histogram("rpc_latency")
            .with_description("Latency in ms of each RPC.")
            .with_unit("ms")
            // Update the version of opentelemetry to support custom buckets.
            //.with_boundaries(vec![0, 100, 200, 300, 400, 500, 1000, 2000, 5000, 50000])
            .init();
        // Initialize the total count to 0 to trigger the metric registration.
        // Otherwise, the metric will only show up once it has been incremented.
        rpc_count.add(0, &[KeyValue::new("request_type", "total")]);
        rpc_failure_count.add(0, &[KeyValue::new("request_type", "total")]);
        rpc_latency.record(1, &[KeyValue::new("request_type", "test")]);
        observer.register_metric(rpc_count.clone());
        observer.register_metric(rpc_failure_count.clone());
        observer.register_metric(rpc_latency.clone());
        Self { rpc_count, rpc_failure_count, rpc_latency }
    }
}

pub fn create_metrics() -> (OakObserver, Arc<Metrics>) {
    let mut observer =
        OakObserver::create("http://10.0.2.100:8080".to_string(), "sealed_memory_service", vec![])
            .unwrap();
    let metrics = Arc::new(Metrics::new(&mut observer));
    (observer, metrics)
}
