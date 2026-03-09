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

#![feature(test)]

extern crate test;

use std::{
    env,
    net::{SocketAddr, TcpStream},
    sync::Arc,
    time::{Duration, Instant},
};

use criterion::{Criterion, criterion_group, criterion_main};
use linux_server::{
    DEFAULT_BORINGSSL_PORT, DEFAULT_NOISE_PORT, DEFAULT_PLAINTEXT_PORT, init_rustls,
    load_certs_and_key,
};
use message_stream_client::{MessageStream, NoiseMessageStream};
use rk_launcher::{OakClientChannelMessageStream, start_rk_enclave_server};
use rustls::{ClientConfig, ServerConfig};
use rustls_pki_types::ServerName;

/// Default VM host address.
const DEFAULT_VM_HOST: &str = "127.0.0.1";

/// Get the VM host from VM_HOST environment variable, or use the default.
fn get_vm_host() -> String {
    env::var("VM_HOST").unwrap_or_else(|_| DEFAULT_VM_HOST.to_string())
}

/// Get the VM address for a specific protocol.
fn get_vm_addr(protocol: &str, default_port: u16) -> SocketAddr {
    let host = get_vm_host();
    let port_env = format!("VM_{}_PORT", protocol.to_uppercase());
    let port: u16 = match env::var(&port_env) {
        Ok(s) => match s.parse() {
            Ok(p) => p,
            Err(e) => {
                eprintln!(
                    "Warning: Failed to parse {}='{}': {}. Using default port {}.",
                    port_env, s, e, default_port
                );
                default_port
            }
        },
        Err(_) => default_port,
    };
    format!("{}:{}", host, port)
        .parse()
        .unwrap_or_else(|e| panic!("Invalid address {}:{}: {}", host, port, e))
}

fn create_message(size: usize) -> Vec<u8> {
    let mut message = vec![0u8; size];
    for (i, msg) in message.iter_mut().enumerate() {
        *msg = (i % 256) as u8;
    }
    message
}

const TEST_SIZES: &[usize] = &[1, 1000, 100_000, 1_000_000, 10_000_000, 100_000_000];

/// Wraps the benchmark logic for a given set of sizes and protocol.
///
/// Note: This benchmark measures the time to send and receive messages of
/// various sizes. It EXCLUDES the time taken to establish the connection and
/// perform any handshake (e.g., Noise or TLS handshake), which happens inside
/// the `stream_creator` closure before the timer starts.
fn benchmark_wrapper(
    sizes: &[usize],
    description: &str,
    c: &mut Criterion,
    mut stream_creator: impl FnMut() -> Box<dyn MessageStream>,
) {
    let mut group = c.benchmark_group(description);

    for size in sizes.iter() {
        group.throughput(criterion::Throughput::Bytes(*size as u64));
        group.bench_with_input(criterion::BenchmarkId::from_parameter(size), size, |b, size| {
            b.iter_custom(|iters| {
                let mut send_total = Duration::from_millis(0);
                let mut recv_total = Duration::from_millis(0);
                for _i in 0..iters {
                    let mut stream = stream_creator();
                    let message = create_message(*size);
                    let start = Instant::now();
                    stream.send_message(message.as_slice());
                    send_total += start.elapsed();
                    let start = Instant::now();
                    let response = stream.read_message();
                    recv_total += start.elapsed();
                    assert_eq!(message, response);
                }
                (send_total + recv_total) / 2
            });
        });
    }

    group.finish();
}
fn plaintext_local_tcp_benchmark(c: &mut Criterion) {
    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(|tcp_stream: TcpStream| -> Box<dyn MessageStream> { Box::new(tcp_stream) }),
    );

    benchmark_wrapper(TEST_SIZES, "Local TCP Plaintext Message Exchange", c, || {
        Box::new(TcpStream::connect(addr).expect("couldn't connect to server"))
    });

    let mut stream = TcpStream::connect(addr).expect("couldn't connect to server");
    stream.send_message(b"exit");
    server_handle.join().unwrap();
}

fn noise_local_tcp_benchmark(c: &mut Criterion) {
    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(|tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            Box::new(NoiseMessageStream::new_server(tcp_stream))
        }),
    );

    benchmark_wrapper(TEST_SIZES, "Local TCP Noise Message Exchange", c, || {
        new_noise_client_stream(addr)
    });

    let mut stream = new_noise_client_stream(addr);
    stream.send_message(b"exit");
    server_handle.join().unwrap();
}

fn boringssl_local_tcp_benchmark(c: &mut Criterion) {
    init_rustls();
    let (certs, key) = load_certs_and_key();

    let server_config = ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(certs.clone(), key)
        .expect("bad certificate/key");
    let server_config = Arc::new(server_config);

    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(move |tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            let conn = rustls::ServerConnection::new(server_config.clone()).unwrap();
            let stream = rustls::StreamOwned::new(conn, tcp_stream);
            Box::new(stream)
        }),
    );

    let mut root_store = rustls::RootCertStore::empty();
    root_store.add(certs[0].clone()).unwrap();
    let client_config =
        ClientConfig::builder().with_root_certificates(root_store).with_no_client_auth();
    let client_config = Arc::new(client_config);

    benchmark_wrapper(TEST_SIZES, "Local TCP BoringSSL Message Exchange", c, || {
        let tcp_stream = TcpStream::connect(addr).expect("couldn't connect to server");
        let server_name = ServerName::try_from("localhost").unwrap().to_owned();
        let conn = rustls::ClientConnection::new(client_config.clone(), server_name).unwrap();
        let stream = rustls::StreamOwned::new(conn, tcp_stream);
        Box::new(stream)
    });

    let tcp_stream = TcpStream::connect(addr).expect("couldn't connect to server");
    let server_name = ServerName::try_from("localhost").unwrap().to_owned();
    let conn = rustls::ClientConnection::new(client_config.clone(), server_name).unwrap();
    let mut stream = rustls::StreamOwned::new(conn, tcp_stream);
    stream.send_message(b"exit");
    server_handle.join().unwrap();
}
fn plaintext_vm_tcp_benchmark(c: &mut Criterion) {
    let addr = get_vm_addr("plaintext", DEFAULT_PLAINTEXT_PORT);
    println!("Connecting to VM at {} for plaintext benchmark", addr);

    benchmark_wrapper(TEST_SIZES, "VM TCP Plaintext Message Exchange", c, || {
        Box::new(TcpStream::connect(addr).expect(
            "Couldn't connect to VM. Make sure the VM is running with:\n\
             ./oak_benchmarks/linux_vm/run_vm.sh --image=<path> --port=5000 --port=5001 --port=5002 --headless",
        ))
    });
}

fn new_noise_client_stream(addr: SocketAddr) -> Box<dyn MessageStream> {
    let tcp_stream = TcpStream::connect(addr).expect("couldn't connect to server");
    Box::new(NoiseMessageStream::new_client(tcp_stream))
}

fn noise_vm_tcp_benchmark(c: &mut Criterion) {
    let addr = get_vm_addr("noise", DEFAULT_NOISE_PORT);
    println!("Connecting to VM at {} for noise benchmark", addr);

    benchmark_wrapper(TEST_SIZES, "VM TCP Noise Message Exchange", c, || {
        new_noise_client_stream(addr)
    });
}

fn boringssl_vm_tcp_benchmark(c: &mut Criterion) {
    let addr = get_vm_addr("boringssl", DEFAULT_BORINGSSL_PORT);
    println!("Connecting to VM at {} for boringssl benchmark", addr);

    init_rustls();
    let (certs, _key) = load_certs_and_key();

    let mut root_store = rustls::RootCertStore::empty();
    root_store.add(certs[0].clone()).unwrap();
    let client_config =
        ClientConfig::builder().with_root_certificates(root_store).with_no_client_auth();
    let client_config = Arc::new(client_config);

    benchmark_wrapper(TEST_SIZES, "VM TCP BoringSSL Message Exchange", c, || {
        let tcp_stream = TcpStream::connect(addr).expect(
            "Couldn't connect to VM. Make sure the VM is running with:\n\
             ./oak_benchmarks/linux_vm/run_vm.sh --image=<path> --port=5000 --port=5001 --port=5002 --headless",
        );
        let server_name = ServerName::try_from("localhost").unwrap().to_owned();
        let conn = rustls::ClientConnection::new(client_config.clone(), server_name).unwrap();
        let stream = rustls::StreamOwned::new(conn, tcp_stream);
        Box::new(stream)
    });
}

fn plaintext_rk_benchmark(c: &mut Criterion) {
    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (guest_instance, oak_client_channel) =
        rt.block_on(async { start_rk_enclave_server(b"plaintext").await });

    benchmark_wrapper(TEST_SIZES, "RK Plaintext Message Exchange", c, || {
        Box::new(OakClientChannelMessageStream::new(&oak_client_channel))
    });
    futures::executor::block_on(async { guest_instance.kill().await })
        .expect("failed to kill instance");
}

fn noise_rk_benchmark(c: &mut Criterion) {
    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (guest_instance, oak_client_channel) =
        rt.block_on(async { start_rk_enclave_server(b"noise").await });

    benchmark_wrapper(TEST_SIZES, "RK Noise Message Exchange", c, || {
        Box::new(NoiseMessageStream::new_client(OakClientChannelMessageStream::new(
            &oak_client_channel,
        )))
    });

    rt.block_on(async { guest_instance.kill().await }).expect("failed to kill instance");
}

criterion_group!(
    benches,
    plaintext_rk_benchmark,
    noise_rk_benchmark,
    plaintext_local_tcp_benchmark,
    noise_local_tcp_benchmark,
    boringssl_local_tcp_benchmark,
    plaintext_vm_tcp_benchmark,
    noise_vm_tcp_benchmark,
    boringssl_vm_tcp_benchmark
);
criterion_main!(benches);
