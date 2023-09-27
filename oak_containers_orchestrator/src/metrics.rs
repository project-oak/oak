//
// Copyright 2023 The Project Oak Authors
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

use anyhow::Result;
use oak_containers_orchestrator_client::{
    proto::openmetrics::{
        self, counter_value::Total, CounterValue, GaugeValue, Label, Metric, MetricFamily,
        MetricPoint, MetricType,
    },
    LauncherClient,
};
use std::{sync::Arc, time::Duration};

fn gauge(name: String, unit: String, help: String, value: i64) -> MetricFamily {
    MetricFamily {
        name,
        r#type: MetricType::Gauge.into(),
        unit,
        help,
        metrics: vec![Metric {
            labels: Vec::new(),
            metric_points: vec![MetricPoint {
                timestamp: None,
                value: Some(openmetrics::metric_point::Value::GaugeValue(GaugeValue {
                    value: Some(openmetrics::gauge_value::Value::IntValue(value)),
                })),
            }],
        }],
    }
}

fn counter(name: String, unit: String, help: String, value: u64) -> MetricFamily {
    MetricFamily {
        name,
        r#type: MetricType::Counter.into(),
        unit,
        help,
        metrics: vec![Metric {
            labels: Vec::new(),
            metric_points: vec![MetricPoint {
                timestamp: None,
                value: Some(openmetrics::metric_point::Value::CounterValue(
                    CounterValue {
                        created: None,
                        exemplar: None,
                        total: Some(Total::IntValue(value)),
                    },
                )),
            }],
        }],
    }
}

fn collect_proc_stat() -> Result<Vec<MetricFamily>> {
    let stats = procfs::KernelStats::new()?;

    let mut metrics = Vec::new();

    let create_cpu_metric = |cpu: usize, mode: &'static str, value: u64| Metric {
        labels: vec![
            Label {
                name: "cpu".to_string(),
                value: cpu.to_string(),
            },
            Label {
                name: "mode".to_string(),
                value: mode.to_string(),
            },
        ],
        metric_points: vec![MetricPoint {
            value: Some(openmetrics::metric_point::Value::CounterValue(
                CounterValue {
                    created: None,
                    exemplar: None,
                    total: Some(Total::IntValue(value)),
                },
            )),
            timestamp: None,
        }],
    };

    let mut cpu_seconds = Vec::new();
    for (cpu, stats) in stats.cpu_time.iter().enumerate() {
        cpu_seconds.push(create_cpu_metric(cpu, "user", stats.user));
        cpu_seconds.push(create_cpu_metric(cpu, "idle", stats.idle));
        cpu_seconds.push(create_cpu_metric(cpu, "nice", stats.nice));
        cpu_seconds.push(create_cpu_metric(cpu, "system", stats.system));
        if let Some(iowait) = stats.iowait {
            cpu_seconds.push(create_cpu_metric(cpu, "iowait", iowait));
        }
        if let Some(irq) = stats.irq {
            cpu_seconds.push(create_cpu_metric(cpu, "irq", irq));
        }
        if let Some(softirq) = stats.irq {
            cpu_seconds.push(create_cpu_metric(cpu, "softirq", softirq));
        }
        if let Some(steal) = stats.steal {
            cpu_seconds.push(create_cpu_metric(cpu, "steal", steal));
        }
    }
    metrics.push(MetricFamily {
        name: "cpu_seconds_total".to_string(),
        r#type: MetricType::Counter.into(),
        unit: "seconds".to_string(),
        help: "Seconds the CPUs spent in each mode.".to_string(),
        metrics: cpu_seconds,
    });

    metrics.push(counter(
        "context_switches_total".to_string(),
        String::new(),
        "Total number of context switches.".to_string(),
        stats.ctxt,
    ));
    metrics.push(counter(
        "forks_total".to_string(),
        String::new(),
        "Total number of forks.".to_string(),
        stats.processes,
    ));
    if let Some(blocked) = stats.procs_blocked {
        gauge(
            "procs_blocked".to_string(),
            String::new(),
            "Number of processes blocked waiting for I/O to complete.".to_string(),
            blocked.into(),
        );
    }
    if let Some(running) = stats.procs_running {
        metrics.push(gauge(
            "procs_running".to_string(),
            String::new(),
            "Number of processes in runnable state.".to_string(),
            running.into(),
        ));
    }

    Ok(metrics)
}

pub async fn run(launcher_client: Arc<LauncherClient>) -> Result<()> {
    let mut interval = tokio::time::interval(Duration::from_secs(60));

    loop {
        interval.tick().await;
        let mut metric_families = Vec::new();
        metric_families.append(&mut collect_proc_stat()?);
        launcher_client
            .push_metrics(metric_families)
            .await
            .map_err(|err| anyhow::anyhow!("failed to push metrics: {}", err))?;
    }
}
