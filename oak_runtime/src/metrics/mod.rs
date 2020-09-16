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
    proto::MetricFamily, HistogramOpts, HistogramVec, IntCounterVec, IntGauge, IntGaugeVec, Opts,
    Registry,
};

pub mod server;

/// Helper struct with functions for creating and registering metrics.
struct MetricsBuilder {
    pub registry: Registry,
}

/// Mostly copied from https://github.com/grpc-ecosystem/java-grpc-prometheus
#[derive(Clone)]
pub struct GrpcServerMetrics {
    pub grpc_server_started_total: IntCounterVec,
    pub grpc_server_handled_total: IntCounterVec,
    pub grpc_server_handled_latency_seconds: HistogramVec,
    pub grpc_server_response_size_bytes: HistogramVec,
    pub grpc_server_msg_sent_total: HistogramVec,
}

/// Mostly copied from https://github.com/grpc-ecosystem/java-grpc-prometheus
#[derive(Clone)]
pub struct GrpcClientMetrics {
    pub grpc_client_started_total: IntCounterVec,
    pub grpc_client_completed: IntCounterVec,
    pub grpc_client_completed_latency_seconds: HistogramVec,
    pub grpc_client_sent_bytes: HistogramVec,
    pub grpc_client_received_bytes: HistogramVec,
    pub grpc_client_received_msgs: HistogramVec,
}

/// Struct that collects all metrics for monitoring the Oak Runtime.
#[derive(Clone)]
pub struct RuntimeMetrics {
    pub runtime_nodes_by_type: IntGaugeVec,
    pub runtime_health_check: IntGauge,
}

/// Struct that collects all the metrics in one place
#[derive(Clone)]
pub struct Metrics {
    registry: Registry,
    pub runtime_metrics: RuntimeMetrics,
    pub grpc_server_metrics: GrpcServerMetrics,
    pub grpc_client_metrics: GrpcClientMetrics,
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

fn int_gauge_vec(metric_name: &str, labels: &[&str], help: &str) -> IntGaugeVec {
    let opts = Opts::new(metric_name, help);
    IntGaugeVec::new(opts, labels).unwrap()
}

impl GrpcServerMetrics {
    fn new(builder: &MetricsBuilder) -> Self {
        GrpcServerMetrics {
            grpc_server_started_total: builder.register(counter_vec(
                "grpc_server_started_total",
                &["method_name"],
                "Total number of RPCs started on the server, for each method invocation.",
            )),
            grpc_server_handled_total: builder.register(counter_vec(
                "grpc_server_handled_total",
                &["method_name", "status_code"],
                "Total number of RPCs completed on the server, for each method invocation, regardless of success or failure.",
            )),
            grpc_server_handled_latency_seconds: builder.register(histogram_vec(
                "grpc_server_handled_latency_seconds",
                &["method_name"],
                "Histogram of response latency of RPCs handled by the server, for each method invocation.",
            )),
            grpc_server_response_size_bytes: builder.register(histogram_vec(
                "grpc_server_response_size_bytes",
                &["method_name"],
                "Histogram of RPC response message sizes sent by the server, for each method invocation.",
            )),
            grpc_server_msg_sent_total: builder.register(histogram_vec(
                "grpc_server_msg_sent_total",
                &["method_name"],
                "Histogram of number of RPC response messages sent by the server, for each method invocation.",
            )),
        }
    }
}

impl GrpcClientMetrics {
    fn new(builder: &MetricsBuilder) -> Self {
        GrpcClientMetrics {
            grpc_client_started_total: builder.register(counter_vec(
                "grpc_client_started_total",
                &["server", "method_name"],
                "Total number of RPCs started on the client, for each method invocation.",
            )),
            grpc_client_completed: builder.register(counter_vec(
                "grpc_client_completed",
                &["server", "method_name", "status_code"],
                "Total number of RPCs completed on the client, for each method invocation, regardless of success or failure.",
            )),
            grpc_client_completed_latency_seconds: builder.register(histogram_vec(
                "grpc_client_completed_latency_seconds",
                &["server", "method_name"],
                "Histogram of RPC response latency for completed RPCs, for each method invocation, in seconds.",
            )),
            grpc_client_sent_bytes: builder.register(histogram_vec(
                "grpc_client_sent_bytes",
                &["server", "method_name"],
                "Histogram of RPC request sizes sent by the client, for each method invocation.",
            )),
            grpc_client_received_bytes: builder.register(histogram_vec(
                "grpc_client_received_bytes",
                &["server", "method_name"],
                "Histogram of RPC response message sizes received by the client, for each method invocation.",
            )),
            grpc_client_received_msgs: builder.register(histogram_vec(
                "grpc_client_received_msgs",
                &["server", "method_name"],
                "Histogram of number of RPC response messages received by the client, for each method invocation.",
            )),
        }
    }

    pub fn observe_new_request(&self, server: &str, method_name: &str, msg_len: usize) {
        self.grpc_client_started_total
            .with_label_values(&[server, method_name])
            .inc();
        self.grpc_client_sent_bytes
            .with_label_values(&[server, method_name])
            .observe(msg_len as f64);
    }

    pub fn observe_new_response_message(&self, server: &str, method_name: &str, msg_len: usize) {
        self.grpc_client_received_bytes
            .with_label_values(&[server, method_name])
            .observe(msg_len as f64);
    }

    pub fn observe_response_handling_completed(
        &self,
        server: &str,
        method_name: &str,
        status_code: &str,
        msg_count: u32,
    ) {
        self.grpc_client_received_msgs
            .with_label_values(&[server, method_name])
            .observe(msg_count as f64);
        self.grpc_client_completed
            .with_label_values(&[server, method_name, status_code])
            .inc();
    }

    pub fn start_timer(&self, server: &str, method_name: &str) -> prometheus::HistogramTimer {
        self.grpc_client_completed_latency_seconds
            .with_label_values(&[server, method_name])
            .start_timer()
    }
}

impl RuntimeMetrics {
    fn new(builder: &MetricsBuilder) -> Self {
        RuntimeMetrics {
            runtime_nodes_by_type: builder.register(int_gauge_vec(
                "runtime_nodes_total",
                &["node_type"],
                "Number of nodes in the runtime, by node type.",
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
            grpc_client_metrics: GrpcClientMetrics::new(&builder),
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
