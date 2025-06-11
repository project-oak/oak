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
use opentelemetry::metrics::Counter;

pub struct Metrics {
    // Total number of RPCs received by the private memory server.
    pub rpc_count: Counter<u64>,
    // Number of RPCs that failed.
    pub rpc_failure_count: Counter<u64>,
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
        observer.register_metric(rpc_count.clone());
        observer.register_metric(rpc_failure_count.clone());
        Self { rpc_count, rpc_failure_count }
    }
}

pub fn create_metrics() -> (OakObserver, Arc<Metrics>) {
    let mut observer = OakObserver::create(
        "http://10.0.2.100:8080".to_string(),
        "sealed_memory_service".to_string(),
        vec![],
    )
    .unwrap();
    let metrics = Arc::new(Metrics::new(&mut observer));
    (observer, metrics)
}
