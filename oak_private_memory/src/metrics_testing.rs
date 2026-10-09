//
// Copyright 2026 The Project Oak Authors
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

//! Helpers for reading back recorded metric values in tests.
//!
//! [`TestMetrics`] builds a fresh [`SdkMeterProvider`] whose periodic reader
//! pushes into an in-test [`PushMetricExporter`], and constructs the metrics
//! struct from its meter. Values are read by calling `force_flush` on the
//! provider, which synchronously collects and exports. This mirrors production
//! wiring (`Metrics::new(&Meter)`) without touching the global metrics
//! singleton, so tests are deterministic and independent of each other.
//!
//! `ManualReader` and `InMemoryMetricExporter` would be simpler, but they are
//! gated behind `opentelemetry_sdk` features that are not enabled in
//! `@oak_crates_index`. `PeriodicReader` spawns a background worker thread per
//! test instance (its 1-hour interval never fires during a test; it's cleaned
//! up on drop). That's fine at this scale, but if the suite grows, enabling
//! the `testing` / in-memory exporter features would avoid the threads.
//!
//! This crate deliberately does not depend on the `metrics` crate: its own
//! unit tests (compiled as a separate copy of that crate) use it too. Pass the
//! constructor in instead, e.g. `TestMetrics::new(metrics::Metrics::new)`.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{Arc, Mutex},
    time::Duration,
};

use opentelemetry::{
    KeyValue,
    metrics::{Meter, MeterProvider as _},
};
use opentelemetry_sdk::{
    error::OTelSdkResult,
    metrics::{
        PeriodicReader, SdkMeterProvider, Temporality,
        data::{AggregatedMetrics, MetricData, ResourceMetrics},
        exporter::PushMetricExporter,
    },
};

/// The `(name, metric)` pairs from a single export.
type ExportedMetrics = Vec<(String, ExportedMetric)>;

/// A [`PushMetricExporter`] that keeps an owned copy of the most recent
/// export so the test can inspect it.
#[derive(Clone, Default)]
struct SnapshotExporter {
    latest: Arc<Mutex<Option<ExportedMetrics>>>,
}

impl PushMetricExporter for SnapshotExporter {
    fn export(
        &self,
        metrics: &ResourceMetrics,
    ) -> impl std::future::Future<Output = OTelSdkResult> + Send {
        let exported = metrics
            .scope_metrics()
            .flat_map(|scope| scope.metrics())
            .map(|metric| {
                (
                    metric.name().to_string(),
                    ExportedMetric {
                        description: metric.description().to_string(),
                        unit: metric.unit().to_string(),
                        data: convert(metric.data()),
                    },
                )
            })
            .collect();
        *self.latest.lock().unwrap() = Some(exported);
        std::future::ready(Ok(()))
    }

    fn force_flush(&self) -> OTelSdkResult {
        Ok(())
    }

    fn shutdown_with_timeout(&self, _timeout: Duration) -> OTelSdkResult {
        Ok(())
    }

    fn temporality(&self) -> Temporality {
        Temporality::Cumulative
    }
}

/// Converts the attributes of an exported data point into sorted [`Attrs`].
fn to_attrs<'a>(key_values: impl Iterator<Item = &'a KeyValue>) -> Attrs {
    let mut attrs: Attrs = key_values
        .map(|key_value| {
            (key_value.key.as_str().to_string(), key_value.value.as_str().into_owned())
        })
        .collect();
    attrs.sort();
    attrs
}

/// Converts exported data into [`Data`]. Only `u64` instruments are handled
/// because every instrument the SMOS `Metrics` struct defines is `u64`; any
/// other data type means a new instrument kind was added, so this panics to
/// make this helper get updated alongside it.
fn convert(data: &AggregatedMetrics) -> Data {
    match data {
        AggregatedMetrics::U64(MetricData::Sum(sum)) => Data::Sum {
            monotonic: sum.is_monotonic(),
            points: sum
                .data_points()
                .map(|point| (to_attrs(point.attributes()), point.value()))
                .collect(),
        },
        AggregatedMetrics::U64(MetricData::Gauge(gauge)) => Data::Gauge(
            gauge
                .data_points()
                .map(|point| (to_attrs(point.attributes()), point.value()))
                .collect(),
        ),
        AggregatedMetrics::U64(MetricData::Histogram(histogram)) => Data::Histogram(
            histogram
                .data_points()
                .map(|point| {
                    (
                        to_attrs(point.attributes()),
                        HistogramPoint {
                            count: point.count(),
                            sum: point.sum(),
                            bounds: point.bounds().collect(),
                            bucket_counts: point.bucket_counts().collect(),
                        },
                    )
                })
                .collect(),
        ),
        other => panic!("unexpected metric data: {other:?}"),
    }
}

/// Sorted `(key, value)` attribute pairs identifying a time series.
pub type Attrs = Vec<(String, String)>;

/// Builds [`Attrs`] from `(key, value)` pairs as written in test expectations.
pub fn attrs(pairs: &[(&str, &str)]) -> Attrs {
    let mut attrs: Attrs =
        pairs.iter().map(|(key, value)| (key.to_string(), value.to_string())).collect();
    attrs.sort();
    attrs
}

/// The upper bound reported for a histogram's overflow bucket.
pub const INF: f64 = f64::INFINITY;

/// A single exported histogram data point.
#[derive(Clone, Debug, PartialEq)]
pub struct HistogramPoint {
    /// Number of recorded samples.
    pub count: u64,
    /// Sum of all recorded samples.
    pub sum: u64,
    /// Upper bound of each bucket except the overflow bucket, so there is one
    /// fewer than `bucket_counts`.
    pub bounds: Vec<f64>,
    /// Number of samples in each bucket, ending with the overflow bucket.
    pub bucket_counts: Vec<u64>,
}

impl HistogramPoint {
    /// Returns `(upper_bound, count)` for every non-empty bucket. The
    /// overflow bucket has an upper bound of [`INF`].
    pub fn nonzero_buckets(&self) -> Vec<(f64, u64)> {
        self.bucket_counts
            .iter()
            .enumerate()
            .filter(|(_, count)| **count > 0)
            .map(|(index, count)| (self.bounds.get(index).copied().unwrap_or(INF), *count))
            .collect()
    }
}

/// The data of one exported metric, keyed by series attributes.
#[derive(Clone, Debug, PartialEq)]
pub enum Data {
    Sum { monotonic: bool, points: BTreeMap<Attrs, u64> },
    Gauge(BTreeMap<Attrs, u64>),
    Histogram(BTreeMap<Attrs, HistogramPoint>),
}

/// One exported metric.
#[derive(Clone, Debug)]
pub struct ExportedMetric {
    /// The instrument's description.
    pub description: String,
    /// The instrument's unit, e.g. `ms`.
    pub unit: String,
    /// The recorded series.
    pub data: Data,
}

/// The metrics exported by a single collection, keyed by metric name.
pub struct Snapshot(BTreeMap<String, ExportedMetric>);

impl Snapshot {
    /// Names of all exported metrics.
    pub fn names(&self) -> BTreeSet<&str> {
        self.0.keys().map(String::as_str).collect()
    }

    /// Returns the metric `name`, panicking if it was not exported.
    pub fn get(&self, name: &str) -> &ExportedMetric {
        self.0
            .get(name)
            .unwrap_or_else(|| panic!("metric {name} not exported; got {:?}", self.names()))
    }

    /// All series of the monotonic counter `name`.
    pub fn counter_points(&self, name: &str) -> &BTreeMap<Attrs, u64> {
        match &self.get(name).data {
            Data::Sum { monotonic: true, points } => points,
            other => panic!("{name} is not a monotonic sum: {other:?}"),
        }
    }

    /// The value of the counter series `name{pairs}`, panicking if absent.
    pub fn counter(&self, name: &str, pairs: &[(&str, &str)]) -> u64 {
        *self
            .counter_points(name)
            .get(&attrs(pairs))
            .unwrap_or_else(|| panic!("{name} has no point for {pairs:?}"))
    }

    /// All series of the gauge `name`.
    pub fn gauge_points(&self, name: &str) -> &BTreeMap<Attrs, u64> {
        match &self.get(name).data {
            Data::Gauge(points) => points,
            other => panic!("{name} is not a gauge: {other:?}"),
        }
    }

    /// The value of the gauge series `name{pairs}`, panicking if absent.
    pub fn gauge(&self, name: &str, pairs: &[(&str, &str)]) -> u64 {
        *self
            .gauge_points(name)
            .get(&attrs(pairs))
            .unwrap_or_else(|| panic!("{name} has no point for {pairs:?}"))
    }

    /// All series of the histogram `name`.
    pub fn histogram_points(&self, name: &str) -> &BTreeMap<Attrs, HistogramPoint> {
        match &self.get(name).data {
            Data::Histogram(points) => points,
            other => panic!("{name} is not a histogram: {other:?}"),
        }
    }

    /// The histogram series `name{pairs}`, panicking if absent.
    pub fn histogram(&self, name: &str, pairs: &[(&str, &str)]) -> &HistogramPoint {
        self.histogram_points(name)
            .get(&attrs(pairs))
            .unwrap_or_else(|| panic!("{name} has no point for {pairs:?}"))
    }
}

/// A metrics struct `M` wired to a private in-memory meter provider.
pub struct TestMetrics<M> {
    /// The metrics instance to hand to the code under test.
    pub metrics: Arc<M>,
    exporter: SnapshotExporter,
    provider: SdkMeterProvider,
}

impl<M> TestMetrics<M> {
    /// Creates a fresh provider and builds `M` from it with `new_metrics`
    /// (e.g. `metrics::Metrics::new`).
    pub fn new(new_metrics: impl FnOnce(&Meter) -> M) -> Self {
        let exporter = SnapshotExporter::default();
        // The interval is irrelevant: tests export via `force_flush`.
        let reader = PeriodicReader::builder(exporter.clone())
            .with_interval(Duration::from_secs(3600))
            .build();
        let provider = SdkMeterProvider::builder().with_reader(reader).build();
        let metrics = Arc::new(new_metrics(&provider.meter("sealed_memory_service_test")));
        Self { metrics, exporter, provider }
    }

    /// Collects and returns all currently exported metrics.
    pub fn collect(&self) -> Snapshot {
        *self.exporter.latest.lock().unwrap() = None;
        self.provider.force_flush().expect("failed to flush metrics");
        let exported = self.exporter.latest.lock().unwrap().take().expect("nothing was exported");
        let mut snapshot = BTreeMap::new();
        for (name, metric) in exported {
            assert!(snapshot.insert(name.clone(), metric).is_none(), "duplicate metric {name}");
        }
        Snapshot(snapshot)
    }
}
