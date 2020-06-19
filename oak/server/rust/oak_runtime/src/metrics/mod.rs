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

//! Functionality to expose metrics from a running Runtime.

use prometheus::{
    proto::MetricFamily, HistogramOpts, HistogramVec, IntCounterVec, IntGauge, Opts, Registry,
};

pub mod server;

/// Helper struct with functions for creating and registering metrics.
struct MetricsBuilder {
    pub registry: Registry,
}

/// Mostly copied from https://github.com/grpc-ecosystem/java-grpc-prometheus
#[derive(Clone)]
pub struct GrpcServerMetrics {
    /// Total number of RPCs started on the server.
    pub grpc_server_started_total: IntCounterVec,
    /// Total number of RPCs completed on the server, regardless of success or failure.
    pub grpc_server_handled_total: IntCounterVec,
    /// Histogram of response latency of RPCs handled by the server, in seconds.
    pub grpc_server_handled_latency_seconds: HistogramVec,
    /// Histogram of response sizes of RPCs handled by the server.
    pub grpc_response_size_bytes: HistogramVec,
    /// Total number of stream messages sent by the server.
    pub grpc_server_msg_sent_total: HistogramVec,
}

/// Struct that collects all metrics for monitoring the Oak Runtime.
#[derive(Clone)]
pub struct RuntimeMetrics {
    pub runtime_nodes_total: IntGauge,
    pub runtime_health_check: IntGauge,
}

/// Struct that collects all the metrics in one place
#[derive(Clone)]
pub struct Metrics {
    registry: Registry,
    pub runtime_metrics: RuntimeMetrics,
    pub grpc_server_metrics: GrpcServerMetrics,
}

impl MetricsBuilder {
    pub fn new() -> Self {
        Self {
            registry: Registry::new(),
        }
    }

    fn register<T: 'static + prometheus::core::Collector + Clone>(&self, metric: T) -> T {
        self.registry.register(Box::new(metric.clone())).unwrap();
        metric
    }
}

fn counter_vec(metric_name: &str, labels: &[&str], help: &str) -> IntCounterVec {
    let opts = Opts::new(metric_name, help);
    IntCounterVec::new(opts, labels).unwrap()
}

fn histogram_vec(metric_name: &str, labels: &[&str], help: &str) -> HistogramVec {
    let opts = HistogramOpts::new(metric_name, help);
    HistogramVec::new(opts, labels).unwrap()
}

fn int_gauge(metric_name: &str, help: &str) -> IntGauge {
    let opts = Opts::new(metric_name, help);
    IntGauge::with_opts(opts).unwrap()
}

impl GrpcServerMetrics {
    fn new(builder: &MetricsBuilder) -> Self {
        GrpcServerMetrics {
            grpc_server_started_total: builder.register(counter_vec(
                "grpc_server_started_total",
                &["method_name"],
                "Total number of RPCs started on the server.",
            )),
            grpc_server_handled_total: builder.register(counter_vec(
                "grpc_server_handled_total",
                &["method_name", "status_code"],
                "Total number of RPCs completed on the server, regardless of success or failure.",
            )),
            grpc_server_handled_latency_seconds: builder.register(histogram_vec(
                "grpc_server_handled_latency_seconds",
                &["method_name"],
                "Histogram of response latency of RPCs handled by the server.",
            )),
            grpc_response_size_bytes: builder.register(histogram_vec(
                "grpc_response_size_bytes",
                &["method_name"],
                "Histogram of response sizes of RPCs handled by the server.",
            )),
            grpc_server_msg_sent_total: builder.register(histogram_vec(
                "grpc_server_msg_sent_total",
                &["method_name"],
                "Total number of RPC response messages sent by the server.",
            )),
        }
    }
}

impl RuntimeMetrics {
    fn new(builder: &MetricsBuilder) -> Self {
        RuntimeMetrics {
            runtime_nodes_total: builder.register(int_gauge(
                "runtime_nodes_total",
                "Number of nodes in the runtime.",
            )),
            runtime_health_check: builder.register(int_gauge(
                "runtime_health_check",
                "Health indicator for the runtime.",
            )),
        }
    }
}

impl Metrics {
    pub fn new() -> Self {
        let builder = MetricsBuilder::new();
        Self {
            runtime_metrics: RuntimeMetrics::new(&builder),
            grpc_server_metrics: GrpcServerMetrics::new(&builder),
            registry: builder.registry,
        }
    }

    pub fn gather(&self) -> Vec<MetricFamily> {
        self.registry.gather()
    }
}

impl Default for Metrics {
    fn default() -> Self {
        Metrics::new()
    }
}
