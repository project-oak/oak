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

use std::time::Duration;

use opentelemetry::{
    global,
    metrics::{
        Counter, Histogram, Meter, MeterProvider, MetricsError, ObservableCounter, ObservableGauge,
        ObservableUpDownCounter, UpDownCounter,
    },
    KeyValue,
};
use opentelemetry_otlp::{ExportConfig, WithExportConfig};
use opentelemetry_sdk::{
    metrics::{
        reader::{DefaultAggregationSelector, DefaultTemporalitySelector},
        Aggregation, Instrument, PeriodicReader, SdkMeterProvider, Stream,
    },
    runtime,
};
use tokio::runtime::Handle;

const EXPORT_PERIOD: u64 = 60;

pub enum MeterInstrument {
    U64Counter(Counter<u64>),
    F64Counter(Counter<f64>),

    F64UpDownCounter(UpDownCounter<f64>),
    I64UpDownCounter(UpDownCounter<i64>),

    U64Histogram(Histogram<u64>),
    F64Histogram(Histogram<f64>),

    U64ObservableCounter(ObservableCounter<u64>),
    F64ObservableCounter(ObservableCounter<f64>),

    F64ObservableUpDownCounter(ObservableUpDownCounter<f64>),
    I64ObservableUpDownCounter(ObservableUpDownCounter<i64>),

    U64ObservableGauge(ObservableGauge<u64>),
    F64ObservableGauge(ObservableGauge<f64>),
    I64ObservableGauge(ObservableGauge<i64>),
}

pub struct OakObserver {
    pub meter: Meter,
    pub metric_registry: Vec<MeterInstrument>,
}

impl OakObserver {
    fn create(
        launcher_addr: String,
        scope: String,
        excluded_metrics: Vec<String>,
    ) -> Result<Self, MetricsError> {
        let export_config = ExportConfig { endpoint: launcher_addr, ..ExportConfig::default() };

        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_export_config(export_config)
            .build_metrics_exporter(
                Box::new(DefaultAggregationSelector::new()),
                Box::new(DefaultTemporalitySelector::new()),
            )?;

        let reader = PeriodicReader::builder(exporter, runtime::Tokio)
            .with_interval(Duration::from_secs(EXPORT_PERIOD))
            .build();
        let mut provider = SdkMeterProvider::builder().with_reader(reader);

        // drop [base] metrics marked excluded
        for metric in excluded_metrics {
            provider = provider.with_view(move |i: &Instrument| {
                if i.name == metric {
                    Some(Stream::new().aggregation(Aggregation::Drop))
                } else {
                    None
                }
            });
        }

        let provider = provider.build();
        global::set_meter_provider(provider.clone());
        let meter = provider.meter(scope);

        Ok(Self { meter, metric_registry: Vec::new() })
    }

    pub fn register_metric<T: Into<MeterInstrument>>(&mut self, i: T) {
        self.metric_registry.push(i.into());
    }
}

pub struct MetricsConfig {
    pub launcher_addr: String,
    pub scope: String,
    pub excluded_metrics: Option<Vec<String>>,
}

pub fn init_metrics(metrics_config: MetricsConfig) -> OakObserver {
    let observer = OakObserver::create(
        metrics_config.launcher_addr,
        metrics_config.scope,
        metrics_config.excluded_metrics.unwrap_or_default(),
    );
    let mut observer = observer.unwrap();
    if let Err(e) = add_base_metrics(&mut observer) {
        eprintln!("Error adding base metrics: {:?}", e);
    }
    observer
}

fn add_base_metrics(observer: &mut OakObserver) -> Result<(), MetricsError> {
    observer.register_metric(
        observer
            .meter
            .u64_observable_counter("tokio_workers_count")
            .with_description("Number of worker threads used by the runtime")
            .with_callback(|counter| {
                if let Ok(num_workers) = Handle::current().metrics().num_workers().try_into() {
                    counter.observe(num_workers, &[]);
                }
            })
            .try_init()?,
    );

    observer.register_metric(
        observer
            .meter
            .u64_observable_counter("tokio_blocking_threads_count")
            .with_description("Number of additional threads used by the runtime")
            .with_callback(|counter| {
                if let Ok(num_blocking_threads) =
                    Handle::current().metrics().num_blocking_threads().try_into()
                {
                    counter.observe(num_blocking_threads, &[]);
                }
            })
            .try_init()?,
    );
    observer.register_metric(
        observer
            .meter
            .u64_observable_counter("tokio_active_tasks")
            .with_description("Number of active tasks in the runtime")
            .with_callback(|counter| {
                if let Ok(active_tasks_count) =
                    Handle::current().metrics().active_tasks_count().try_into()
                {
                    counter.observe(active_tasks_count, &[]);
                }
            })
            .try_init()?,
    );
    observer.register_metric(
        observer
            .meter
            .u64_observable_counter("tokio_injection_queue_depth")
            .with_description("Number of tasks currently in the runtime's injection queue")
            .with_callback(|counter| {
                if let Ok(injection_queue_depth) =
                    Handle::current().metrics().injection_queue_depth().try_into()
                {
                    counter.observe(injection_queue_depth, &[]);
                }
            })
            .try_init()?,
    );
    observer.register_metric(
        observer
            .meter
            .u64_observable_counter("tokio_worker_local_queue_depth")
            .with_description("Number of tasks currently scheduled in the workers' local queue")
            .with_callback(|counter| {
                let metrics = Handle::current().metrics();
                for worker in 0..metrics.num_workers() {
                    if let (Ok(depth), Ok(worker)) =
                        (metrics.worker_local_queue_depth(worker).try_into(), worker.try_into())
                    {
                        counter.observe(depth, &[KeyValue::new::<&str, i64>("worker", worker)])
                    }
                }
            })
            .try_init()?,
    );
    Ok(())
}

impl From<Counter<u64>> for MeterInstrument {
    fn from(val: Counter<u64>) -> Self {
        MeterInstrument::U64Counter(val)
    }
}

impl From<Counter<f64>> for MeterInstrument {
    fn from(val: Counter<f64>) -> Self {
        MeterInstrument::F64Counter(val)
    }
}

impl From<UpDownCounter<f64>> for MeterInstrument {
    fn from(val: UpDownCounter<f64>) -> Self {
        MeterInstrument::F64UpDownCounter(val)
    }
}

impl From<UpDownCounter<i64>> for MeterInstrument {
    fn from(val: UpDownCounter<i64>) -> Self {
        MeterInstrument::I64UpDownCounter(val)
    }
}

impl From<Histogram<u64>> for MeterInstrument {
    fn from(val: Histogram<u64>) -> Self {
        MeterInstrument::U64Histogram(val)
    }
}

impl From<Histogram<f64>> for MeterInstrument {
    fn from(val: Histogram<f64>) -> Self {
        MeterInstrument::F64Histogram(val)
    }
}

impl From<ObservableCounter<u64>> for MeterInstrument {
    fn from(val: ObservableCounter<u64>) -> Self {
        MeterInstrument::U64ObservableCounter(val)
    }
}

impl From<ObservableCounter<f64>> for MeterInstrument {
    fn from(val: ObservableCounter<f64>) -> Self {
        MeterInstrument::F64ObservableCounter(val)
    }
}

impl From<ObservableUpDownCounter<f64>> for MeterInstrument {
    fn from(val: ObservableUpDownCounter<f64>) -> Self {
        MeterInstrument::F64ObservableUpDownCounter(val)
    }
}

impl From<ObservableUpDownCounter<i64>> for MeterInstrument {
    fn from(val: ObservableUpDownCounter<i64>) -> Self {
        MeterInstrument::I64ObservableUpDownCounter(val)
    }
}

impl From<ObservableGauge<u64>> for MeterInstrument {
    fn from(val: ObservableGauge<u64>) -> Self {
        MeterInstrument::U64ObservableGauge(val)
    }
}

impl From<ObservableGauge<f64>> for MeterInstrument {
    fn from(val: ObservableGauge<f64>) -> Self {
        MeterInstrument::F64ObservableGauge(val)
    }
}

impl From<ObservableGauge<i64>> for MeterInstrument {
    fn from(val: ObservableGauge<i64>) -> Self {
        MeterInstrument::I64ObservableGauge(val)
    }
}
