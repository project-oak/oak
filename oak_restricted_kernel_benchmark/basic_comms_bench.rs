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

use std::time::{Duration, Instant};

use criterion::{criterion_group, criterion_main, Criterion};
use oak_file_utils::data_path;
use oak_launcher_utils::launcher::{self, GuestInstance};

async fn start_rk_enclave_server() -> (Box<dyn GuestInstance>, Box<dyn oak_channel::Channel>) {
    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");

    let initial_data_version = launcher::InitialDataVersion::V1;
    let communication_channel = launcher::CommunicationChannel::VirtioConsole;
    let kernel = data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    );

    let app = data_path("oak_restricted_kernel_benchmark/basic_comms_enclave_app");
    let params = launcher::Params {
        kernel,
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(app),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
        initial_data_version,
        communication_channel,
        vm_type: launcher::VmType::Default,
    };
    println!("launcher params: {:#?}", params);

    let (guest_instance, _connector_handle) =
        launcher::launch(params).await.expect("failed to launch");

    let read_timeout = Duration::from_secs(5);
    let write_timeout = Duration::from_secs(5);
    let oak_channel = guest_instance
        .connect_with_timeouts(read_timeout, write_timeout)
        .await
        .expect("couldn't get connector handle");
    (guest_instance, oak_channel)
}

fn test_read_speeds(c: &mut Criterion) {
    let _ = env_logger::try_init();

    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (_instance, mut channel) = rt.block_on(async { start_rk_enclave_server().await });

    let mut group = c.benchmark_group("Read From Enclave");
    // Gets pretty slow past 10000
    for size in [1u32, 100, 10_000] {
        group.throughput(criterion::Throughput::Bytes(size as u64));
        group.bench_with_input(criterion::BenchmarkId::from_parameter(size), &size, |b, size| {
            b.iter_custom(|iters| {
                let mut total = Duration::from_millis(0);
                for _i in 0..iters {
                    // Command 2: read
                    channel.write_all(&[2]).expect("failed to write command");
                    // Send Size
                    channel.write_all(&(u32::to_le_bytes(*size))).expect("failed to write size");
                    // Read bytes from RK
                    let start = Instant::now();
                    let mut buf = vec![0u8; *size as usize];
                    channel.read_exact(&mut buf).expect("failed to read response");
                    total += start.elapsed();
                }
                total
            });
        });
    }
    group.finish();
}

fn test_write_speeds(c: &mut Criterion) {
    let _ = env_logger::try_init();

    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (_instance, mut channel) = rt.block_on(async { start_rk_enclave_server().await });

    let mut group = c.benchmark_group("Write To Enclave");
    for size in [1u32, 100, 10_000, 10_000_000] {
        group.throughput(criterion::Throughput::Bytes(size as u64));
        group.bench_with_input(criterion::BenchmarkId::from_parameter(size), &size, |b, size| {
            b.iter_custom(|iters| {
                let mut total = Duration::from_millis(0);
                for _i in 0..iters {
                    // Command 1: read
                    channel.write_all(&[1]).expect("failed to write command");
                    // Send Size
                    channel.write_all(&(u32::to_le_bytes(*size))).expect("failed to write size");
                    // Write bytes
                    let buf = vec![0u8; *size as usize];
                    let start = Instant::now();
                    channel.write_all(buf.as_slice()).expect("failed to write message");
                    // Await single ack byte
                    let mut ack_buf = [0u8; 1];
                    channel.read_exact(&mut ack_buf).expect("failed to read response");
                    total += start.elapsed();
                }
                total
            });
        });
    }
    group.finish();
}

criterion_group!(benches, test_read_speeds, test_write_speeds);
criterion_main!(benches);
