//
// Copyright 2024 The Project Oak Authors
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

use std::{future::Future, pin::Pin, time::Instant};

use opentelemetry::{
    KeyValue, global,
    metrics::{Counter, Histogram, Meter, MeterProvider},
};
use opentelemetry_otlp::{ExporterBuildError, WithExportConfig};
use opentelemetry_sdk::metrics::{Aggregation, Instrument, SdkMeterProvider, Stream};

/// Entry point for creating OpenTelemetry instruments.
///
/// Instruments created from `meter` don't need to be stored anywhere to keep
/// exporting:
/// - Observable instruments (`*_observable_counter`, `*_observable_gauge`):
///   `build()` hands the callback to the meter provider, which invokes it on
///   every collection for the provider's lifetime. The returned handle is an
///   empty marker and can be dropped. The `build()` call itself is what
///   registers the callback, so it must not be removed.
/// - Synchronous instruments (`Counter`, `Histogram`, ...): the provider keeps
///   their aggregated state; the code that records values owns the handle.
pub struct OakObserver {
    pub meter: Meter,
}

impl OakObserver {
    pub fn create(
        launcher_addr: String,
        scope: &'static str,
        excluded_metrics: Vec<String>,
    ) -> Result<Self, ExporterBuildError> {
        if tokio::runtime::Handle::try_current().is_err() {
            let provider = SdkMeterProvider::builder().build();
            let meter = provider.meter(scope);
            return Ok(Self { meter });
        }

        let exporter = opentelemetry_otlp::MetricExporter::builder()
            .with_tonic()
            .with_endpoint(launcher_addr)
            .build()?;

        // The default exporter period is 60s.
        // It can be conifgured with OTEL_METRIC_EXPORT_INTERVAL environment variable.
        // See:https://docs.rs/opentelemetry_sdk/0.28.0/opentelemetry_sdk/metrics/struct.MeterProviderBuilder.html#method.with_periodic_exporter
        let mut provider = SdkMeterProvider::builder().with_periodic_exporter(exporter);

        // drop [base] metrics marked excluded
        for metric in excluded_metrics {
            provider = provider.with_view(move |i: &Instrument| {
                if i.name() == metric {
                    Some(
                        Stream::builder()
                            .with_aggregation(Aggregation::Drop)
                            .build()
                            .expect("failed to make stream"),
                    )
                } else {
                    None
                }
            });
        }

        let provider = provider.build();
        global::set_meter_provider(provider.clone());
        let meter = provider.meter(scope);

        if tokio::runtime::Handle::try_current().is_ok()
            && let Err(e) = provider.force_flush()
        {
            eprintln!("failed to flush metrics: {:?}", e);
        }

        Ok(Self { meter })
    }

    pub fn create_monitoring_layer(&self) -> MonitoringLayer {
        MonitoringLayer::new(self.meter.clone())
    }
}

pub struct MetricsConfig {
    pub launcher_addr: String,
    pub scope: &'static str,
    pub excluded_metrics: Option<Vec<String>>,
}

pub fn init_metrics(metrics_config: MetricsConfig, handle: tokio::runtime::Handle) -> OakObserver {
    let observer = OakObserver::create(
        metrics_config.launcher_addr,
        metrics_config.scope,
        metrics_config.excluded_metrics.unwrap_or_default(),
    );
    let observer = observer.unwrap();
    if let Err(e) = add_base_metrics(&observer, handle) {
        eprintln!("Error adding base metrics: {:?}", e);
    }
    observer
}

/// Registers callbacks that report tokio runtime metrics on every export.
///
/// Each `build()` registers its callback with the meter provider; the returned
/// handles are intentionally dropped (see [`OakObserver`]).
fn add_base_metrics(observer: &OakObserver, handle: tokio::runtime::Handle) -> Result<(), ()> {
    observer
        .meter
        .u64_observable_gauge("tokio_workers_count")
        .with_description("Number of worker threads used by the runtime")
        .with_callback({
            let metrics = handle.metrics().clone();
            move |counter| {
                if let Ok(num_workers) = metrics.num_workers().try_into() {
                    counter.observe(num_workers, &[]);
                }
            }
        })
        .build();

    observer
        .meter
        .u64_observable_gauge("tokio_blocking_threads_count")
        .with_description("Number of additional threads used by the runtime")
        .with_callback({
            let metrics = handle.metrics().clone();
            move |counter| {
                if let Ok(num_blocking_threads) = metrics.num_blocking_threads().try_into() {
                    counter.observe(num_blocking_threads, &[]);
                }
            }
        })
        .build();

    observer
        .meter
        .u64_observable_gauge("tokio_active_tasks")
        .with_description("Number of active tasks in the runtime")
        .with_callback({
            let metrics = handle.metrics().clone();
            move |counter| {
                if let Ok(active_tasks_count) = metrics.num_alive_tasks().try_into() {
                    counter.observe(active_tasks_count, &[]);
                }
            }
        })
        .build();

    observer
        .meter
        .u64_observable_gauge("tokio_injection_queue_depth")
        .with_description("Number of tasks currently in the runtime's injection queue")
        .with_callback({
            let metrics = handle.metrics().clone();
            move |counter| {
                if let Ok(injection_queue_depth) = metrics.global_queue_depth().try_into() {
                    counter.observe(injection_queue_depth, &[]);
                }
            }
        })
        .build();

    observer
        .meter
        .u64_observable_gauge("tokio_worker_local_queue_depth")
        .with_description("Number of tasks currently scheduled in the workers' local queue")
        .with_callback({
            let metrics = handle.metrics().clone();
            move |counter| {
                for worker in 0..metrics.num_workers() {
                    if let (Ok(depth), Ok(worker)) =
                        (metrics.worker_local_queue_depth(worker).try_into(), worker.try_into())
                    {
                        counter.observe(depth, &[KeyValue::new::<&str, i64>("worker", worker)])
                    }
                }
            }
        })
        .build();
    Ok(())
}

#[derive(Clone)]
pub struct MonitoringLayer {
    meter: Meter,
}

impl MonitoringLayer {
    fn new(meter: Meter) -> Self {
        Self { meter }
    }
}

impl<S> tower::Layer<S> for MonitoringLayer {
    type Service = MonitoringService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        MonitoringService {
            inner,
            latencies: self
                .meter
                .u64_histogram("rpc_server_latency")
                .with_unit("milliseconds")
                .with_description("Distribution of server-side RPC latency")
                .build(),
            rpc_count: self.meter.u64_counter("rpc_count").build(),
        }
    }
}

#[derive(Clone)]
pub struct MonitoringService<S> {
    inner: S,
    latencies: Histogram<u64>,
    rpc_count: Counter<u64>,
}

impl<S, T> tower::Service<http::Request<T>> for MonitoringService<S>
where
    S: tower::Service<http::Request<T>> + Clone + Send + 'static,
    <S as tower::Service<http::Request<T>>>::Future: Send,
    T: Send + 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(
        &mut self,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: http::Request<T>) -> Self::Future {
        // `[...]/Service/Method`, but we count from right, so method is last
        let mut attributes = Vec::new();
        let mut parts = req.uri().path().rsplitn(3, '/');
        if let Some(method) = parts.next() {
            attributes.push(KeyValue::new("rpc_method", method.to_string()));
        }
        if let Some(service) = parts.next() {
            attributes.push(KeyValue::new("rpc_service_name", service.to_string()));
        }

        // copied from the example in `tower::Service` to guarantee that `poll_ready`
        // has been called on the proper instance (and not the clone!)
        let clone = self.inner.clone();
        let mut inner = std::mem::replace(&mut self.inner, clone);

        let latencies = self.latencies.clone();
        self.rpc_count.add(1, &attributes);

        Box::pin(async move {
            let now = Instant::now();
            let resp = inner.call(req).await;
            latencies.record(now.elapsed().as_micros().try_into().unwrap_or(u64::MAX), &attributes);
            resp
        })
    }
}
