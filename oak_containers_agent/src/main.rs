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
//

#![feature(c_size_t)]

use clap::Parser;
use opentelemetry::{
    global::set_error_handler,
    metrics::{AsyncInstrument, Meter, MeterProvider, ObservableCounter, ObservableGauge, Unit},
    KeyValue,
};
use procfs::{Current, CurrentSI};
use tokio::time::{self, Duration};

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,
}

// It's not dead, it's just asynchronous.
#[allow(dead_code)]
pub struct SystemMetrics {
    cpu_seconds_total: ObservableCounter<u64>,
    context_switches_total: ObservableCounter<u64>,
    forks_total: ObservableCounter<u64>,
    procs_blocked: ObservableGauge<u64>,
    procs_running: ObservableGauge<u64>,

    // Network-related metrics
    net_recv_bytes: ObservableCounter<u64>,
    net_recv_packets: ObservableCounter<u64>,
    net_recv_errs: ObservableCounter<u64>,
    net_sent_bytes: ObservableCounter<u64>,
    net_sent_packets: ObservableCounter<u64>,
    net_sent_errs: ObservableCounter<u64>,

    // Memory-related metrics
    mem_total: ObservableGauge<u64>,
    mem_free: ObservableGauge<u64>,
    mem_available: ObservableGauge<u64>,
    mem_buffers: ObservableGauge<u64>,
    mem_cached: ObservableGauge<u64>,
    mem_slab: ObservableGauge<u64>,
}

#[allow(dead_code)]
impl SystemMetrics {
    fn new(meter: Meter) -> Result<Self, anyhow::Error> {
        Ok(Self {
            cpu_seconds_total: meter
                .u64_observable_counter("cpu_seconds_total")
                .with_unit(Unit::new("seconds"))
                .with_callback(Self::cpu_seconds_total)
                .try_init()?,
            context_switches_total: meter
                .u64_observable_counter("context_switches_total")
                .with_callback(Self::context_switches_total)
                .try_init()?,
            forks_total: meter
                .u64_observable_counter("forks_total")
                .with_callback(Self::forks_total)
                .try_init()?,
            procs_blocked: meter
                .u64_observable_gauge("procs_blocked")
                .with_callback(Self::procs_blocked)
                .try_init()?,
            procs_running: meter
                .u64_observable_gauge("procs_running")
                .with_callback(Self::procs_running)
                .try_init()?,
            net_recv_bytes: meter
                .u64_observable_counter("network_receive_bytes")
                .with_unit(Unit::new("bytes"))
                .with_callback(Self::net_recv_bytes)
                .try_init()?,
            net_recv_packets: meter
                .u64_observable_counter("network_receive_packets")
                .with_callback(Self::net_recv_packets)
                .try_init()?,
            net_recv_errs: meter
                .u64_observable_counter("network_receive_errors")
                .with_callback(Self::net_recv_errs)
                .try_init()?,
            net_sent_bytes: meter
                .u64_observable_counter("network_transmit_bytes")
                .with_unit(Unit::new("bytes"))
                .with_callback(Self::net_sent_bytes)
                .try_init()?,
            net_sent_packets: meter
                .u64_observable_counter("network_transmit_packets")
                .with_callback(Self::net_sent_packets)
                .try_init()?,
            net_sent_errs: meter
                .u64_observable_counter("network_transmit_errors")
                .with_callback(Self::net_sent_errs)
                .try_init()?,
            mem_total: meter
                .u64_observable_gauge("mem_total")
                .with_callback(Self::mem_total)
                .try_init()?,
            mem_free: meter
                .u64_observable_gauge("mem_free")
                .with_callback(Self::mem_free)
                .try_init()?,
            mem_available: meter
                .u64_observable_gauge("mem_available")
                .with_callback(Self::mem_available)
                .try_init()?,
            mem_buffers: meter
                .u64_observable_gauge("mem_buffers")
                .with_callback(Self::mem_buffers)
                .try_init()?,
            mem_cached: meter
                .u64_observable_gauge("mem_cached")
                .with_callback(Self::mem_cached)
                .try_init()?,
            mem_slab: meter
                .u64_observable_gauge("mem_slab")
                .with_callback(Self::mem_slab)
                .try_init()?,
        })
    }

    fn cpu_seconds_total(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::KernelStats::current().unwrap();

        for (cpu, stats) in stats.cpu_time.iter().enumerate() {
            let attributes =
                |mode| [KeyValue::new("cpu", cpu.to_string()), KeyValue::new("mode", mode)];

            counter.observe(stats.user, &attributes("user"));
            counter.observe(stats.idle, &attributes("idle"));
            counter.observe(stats.nice, &attributes("nice"));
            counter.observe(stats.system, &attributes("system"));
            if let Some(iowait) = stats.iowait {
                counter.observe(iowait, &attributes("iowait"));
            }
            if let Some(irq) = stats.irq {
                counter.observe(irq, &attributes("irq"));
            }
            if let Some(softirq) = stats.softirq {
                counter.observe(softirq, &attributes("softirq"));
            }
            if let Some(steal) = stats.steal {
                counter.observe(steal, &attributes("steal"));
            }
        }
    }

    fn context_switches_total(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::KernelStats::current().unwrap();
        counter.observe(stats.ctxt, &[]);
    }

    fn forks_total(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::KernelStats::current().unwrap();
        counter.observe(stats.processes, &[]);
    }

    fn procs_blocked(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::KernelStats::current().unwrap();
        if let Some(procs_blocked) = stats.procs_blocked {
            gauge.observe(procs_blocked.into(), &[]);
        }
    }

    fn procs_running(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::KernelStats::current().unwrap();
        if let Some(procs_running) = stats.procs_running {
            gauge.observe(procs_running.into(), &[]);
        }
    }

    fn net_recv_bytes(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::net::dev_status().unwrap();

        for (interface, stats) in stats {
            counter.observe(stats.recv_bytes, &[KeyValue::new("device", interface)]);
        }
    }

    fn net_recv_packets(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::net::dev_status().unwrap();

        for (interface, stats) in stats {
            counter.observe(stats.recv_packets, &[KeyValue::new("device", interface)]);
        }
    }

    fn net_recv_errs(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::net::dev_status().unwrap();

        for (interface, stats) in stats {
            counter.observe(stats.recv_errs, &[KeyValue::new("device", interface)]);
        }
    }

    fn net_sent_bytes(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::net::dev_status().unwrap();

        for (interface, stats) in stats {
            counter.observe(stats.sent_bytes, &[KeyValue::new("device", interface)]);
        }
    }

    fn net_sent_packets(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::net::dev_status().unwrap();

        for (interface, stats) in stats {
            counter.observe(stats.sent_packets, &[KeyValue::new("device", interface)]);
        }
    }

    fn net_sent_errs(counter: &dyn AsyncInstrument<u64>) {
        let stats = procfs::net::dev_status().unwrap();

        for (interface, stats) in stats {
            counter.observe(stats.sent_errs, &[KeyValue::new("device", interface)]);
        }
    }

    fn mem_total(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::Meminfo::current().unwrap();
        gauge.observe(stats.mem_total, &[]);
    }

    fn mem_free(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::Meminfo::current().unwrap();
        gauge.observe(stats.mem_free, &[]);
    }

    fn mem_available(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::Meminfo::current().unwrap();
        if let Some(mem_available) = stats.mem_available {
            gauge.observe(mem_available, &[]);
        }
    }

    fn mem_buffers(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::Meminfo::current().unwrap();
        gauge.observe(stats.buffers, &[]);
    }

    fn mem_cached(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::Meminfo::current().unwrap();
        gauge.observe(stats.cached, &[]);
    }

    fn mem_slab(gauge: &dyn AsyncInstrument<u64>) {
        let stats = procfs::Meminfo::current().unwrap();
        gauge.observe(stats.slab, &[]);
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    set_error_handler(|err| eprintln!("oak-agent: OTLP error: {}", err))?;

    let meter_provider = oak_containers_agent::metrics::init_metrics(args.launcher_addr).unwrap();
    let meter = meter_provider.meter("oak_agent");
    let _system_metrics = SystemMetrics::new(meter);

    // keep alive loop
    loop {
        time::sleep(Duration::from_secs(30)).await;
    }
}
