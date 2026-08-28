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
    DEFAULT_NOISE_PORT, DEFAULT_PLAINTEXT_PORT, DEFAULT_TLS_PORT, init_rustls, load_certs_and_key,
};
use message_stream_client::{MessageStream, NoiseMessageStream, control};
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

/// Hands a channel back to the server and waits for it to say so.
///
/// See [`control::CLOSE`] for why the acknowledgement is required rather than
/// just closing the socket.
fn close_channel(stream: &mut dyn MessageStream) {
    stream.send_message(control::CLOSE);
    let ack = stream.read_message();
    assert_eq!(ack, control::CLOSE, "server did not acknowledge close");
}

/// Measures steady-state message exchange over a single long-lived channel.
///
/// One channel is established for the whole measurement and reused for every
/// iteration, so what is timed is a send plus a receive and nothing else.
/// This is the "single channel setup" arm of the comparison the evaluation
/// plan asks for; [`handshake_wrapper`] is the "handshake-per-RPC" arm, and
/// the per-RPC cost of a protocol is the sum of the two.
///
/// It used to open a fresh channel per iteration, untimed. That was not a
/// neutral choice. The connect was excluded from the reported figure but not
/// from the machine, and on the VM legs the resulting connection churn
/// through QEMU's user-mode networking dominated: two of six points came back
/// with confidence intervals spanning more than an order of magnitude, and
/// plaintext -- which churned hardest, because criterion runs the most
/// iterations on the fastest leg -- came out slower than both encrypted legs.
///
/// The reported figure is `(send + recv) / 2`, a mean one-way latency, not a
/// round trip. Halving is what makes the legs comparable -- a round trip
/// through a leg with an asymmetric protocol is not the same quantity -- but
/// it does mean the number must not be quoted as an RTT.
///
/// The channel is created lazily, on the first iteration rather than up
/// front, so that filtering the benchmarks with `--bench <regex>` does not
/// make the VM legs demand a running VM they were told not to measure.
/// Criterion runs every group function regardless of the filter.
fn benchmark_wrapper(
    sizes: &[usize],
    description: &str,
    c: &mut Criterion,
    mut stream_creator: impl FnMut() -> Box<dyn MessageStream>,
) {
    let mut group = c.benchmark_group(description);
    let mut channel: Option<Box<dyn MessageStream>> = None;

    for size in sizes.iter() {
        group.throughput(criterion::Throughput::Bytes(*size as u64));
        group.bench_with_input(criterion::BenchmarkId::from_parameter(size), size, |b, size| {
            b.iter_custom(|iters| {
                let stream = channel.get_or_insert_with(&mut stream_creator);
                let mut send_total = Duration::from_millis(0);
                let mut recv_total = Duration::from_millis(0);
                let message = create_message(*size);
                for _i in 0..iters {
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

    if let Some(mut stream) = channel {
        close_channel(&mut *stream);
    }
}

/// How long to wait, untimed, between tearing one channel down and timing the
/// next one up.
///
/// A connect issued while the previous connection's teardown is still in
/// flight is slower, and without this wait the `Setup` figure is roughly twice
/// its true value and far too noisy to use (plaintext: 33.3 µs ±22% at 0 µs,
/// 16.4 µs ±1.6% at 200 µs). The effect is a threshold, not a slope -- almost
/// all of it is recovered by 25 µs -- so 200 µs deliberately over-provisions to
/// cover the slower VM legs as well.
///
/// It is not free: it costs the TLS leg about 2% and Noise about 1%, because
/// the server thread now goes idle between iterations and the timed handshake
/// includes waking it. That is a reason to keep it rather than shorten it, as a
/// real server is not spinning in wait for the next connection.
///
/// See the README for the interval sweep, the cost table, and the two
/// mechanisms that were ruled out.
const SETUP_SETTLE: Duration = Duration::from_micros(200);

/// Spins for `duration` without sleeping.
///
/// Deliberately a busy wait, so that the client core stays in the state the
/// measurement is supposed to characterise rather than paying a wake-up inside
/// the following timed region.
fn spin_for(duration: Duration) {
    let start = Instant::now();
    while start.elapsed() < duration {
        core::hint::spin_loop();
    }
}

/// Times channel setup: the transport connect plus whatever handshake the leg
/// performs.
///
/// The evaluation plan asks for handshake latency as a metric in its own right
/// -- "Time-to-First-Byte starting from TCP connection establishment,
/// inclusive of the handshake and session key derivation" -- and the README
/// has long claimed this crate measures it. It did not: every handshake
/// happened inside `stream_creator`, outside every timer.
///
/// Each iteration then closes the channel and waits [`SETUP_SETTLE`], both
/// untimed. The close is required because the server serves one channel at a
/// time. The wait is required because a connect issued immediately after a
/// teardown is measurably slower than one issued a round trip later; see
/// [`SETUP_SETTLE`] for the measurements behind that.
///
/// The plaintext leg is the baseline here. It has no handshake, so what it
/// reports is the cost of the transport alone, and the interesting quantity
/// for the other legs is their distance from it.
fn handshake_wrapper(
    description: &str,
    c: &mut Criterion,
    mut stream_creator: impl FnMut() -> Box<dyn MessageStream>,
) {
    let mut group = c.benchmark_group(description);

    group.bench_function("setup", |b| {
        b.iter_custom(|iters| {
            let mut total = Duration::from_millis(0);
            for _i in 0..iters {
                let start = Instant::now();
                let mut stream = stream_creator();
                total += start.elapsed();

                close_channel(&mut *stream);
                spin_for(SETUP_SETTLE);
            }
            total
        });
    });

    group.finish();
}

fn plaintext_local_tcp_benchmark(c: &mut Criterion) {
    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(|tcp_stream: TcpStream| -> Box<dyn MessageStream> { Box::new(tcp_stream) }),
    );

    let connect = || -> Box<dyn MessageStream> {
        Box::new(linux_server::connect(addr).expect("couldn't connect to server"))
    };

    benchmark_wrapper(TEST_SIZES, "Local TCP Plaintext Message Exchange", c, connect);
    handshake_wrapper("Local TCP Plaintext Setup", c, connect);

    let mut stream = linux_server::connect(addr).expect("couldn't connect to server");
    stream.send_message(control::EXIT);
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
    handshake_wrapper("Local TCP Noise Setup", c, || new_noise_client_stream(addr));

    let mut stream = new_noise_client_stream(addr);
    stream.send_message(control::EXIT);
    server_handle.join().unwrap();
}

/// Builds the client configuration for the rustls legs, with session
/// resumption **disabled**.
///
/// One `ClientConfig` is shared across every iteration of a leg, and
/// `Resumption::default()` is an in-memory store of 256 sessions, so leaving it
/// on means the first handshake is full and every subsequent one is a PSK
/// resumption. Confirmed by printing
/// [`rustls::ClientConnection::handshake_kind`] from this code path: iteration
/// 0 reports `Full` and iterations 1 through 6000 all report `Resumed`.
/// [`new_tls_client_stream`] now asserts this on every iteration rather than
/// leaving it to a one-off observation, because the setting is remote from the
/// measurement and its failure mode is silent.
///
/// A resumed TLS 1.3 handshake sends no certificate and generates no
/// signature, so it is a different protocol exchange from the one `Setup`
/// claims to measure, and it is not what the BoringSSL leg does -- that one
/// reports `full_handshakes` equal to its iteration count. With resumption on,
/// `Setup` reported ~180 µs; with it off, ~652 µs. The BoringSSL leg's full
/// handshake is ~601 µs, and those two agreeing to within 8% is the check that
/// both are now doing the same work.
///
/// Resumption is a real and important optimisation, and a client that really
/// did reconnect to the same server for every RPC would benefit from it. It is
/// disabled here because the point of this group is to compare handshake cost
/// across three protocols, and Noise has no resumption mechanism to offer, so
/// the only exchange all three can perform is a full one.
fn tls_client_config(root_store: rustls::RootCertStore) -> Arc<ClientConfig> {
    let mut client_config =
        ClientConfig::builder().with_root_certificates(root_store).with_no_client_auth();
    client_config.resumption = rustls::client::Resumption::disabled();
    Arc::new(client_config)
}

/// Completes the TLS handshake on an already-connected socket.
///
/// `rustls::StreamOwned::new` does not handshake; rustls defers that to the
/// first read or write. Left alone, the handshake therefore lands inside
/// whatever region the caller times next, which is how the message-exchange
/// benchmark came to charge TLS for a handshake while charging Noise for none
/// of its own -- the two legs were not measuring the same thing.
///
/// `complete_io` drives the handshake to completion here, so the cost is
/// attributed to setup on every leg alike, and [`handshake_wrapper`] can see
/// it at all.
///
/// Takes a connected socket rather than an address so that each caller keeps
/// its own connect-failure message; the VM legs need to say how to start the
/// VM.
///
/// Asserts on every iteration that the handshake really was a full one. The
/// resumption setting lives in [`tls_client_config`], several call frames away,
/// and a default-constructed `ClientConfig` resumes; this defect went unnoticed
/// precisely because a resumed handshake is silent and merely fast.
/// `FullWithHelloRetryRequest` is rejected too: it is a full handshake, but it
/// spends an extra round trip, so it is not the exchange the other two legs
/// perform either.
fn new_tls_client_stream(
    tcp_stream: TcpStream,
    client_config: Arc<ClientConfig>,
) -> Box<dyn MessageStream> {
    let server_name = ServerName::try_from("localhost").unwrap().to_owned();
    let conn = rustls::ClientConnection::new(client_config, server_name).unwrap();
    let mut stream = rustls::StreamOwned::new(conn, tcp_stream);
    stream.conn.complete_io(&mut stream.sock).expect("tls handshake failed");
    assert_eq!(
        stream.conn.handshake_kind(),
        Some(rustls::HandshakeKind::Full),
        "the tls leg must perform a full handshake, otherwise it is not measuring \
         the same exchange as the noise and boringssl legs"
    );
    Box::new(stream)
}

fn tls_local_tcp_benchmark(c: &mut Criterion) {
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
    let client_config = tls_client_config(root_store);

    let tls_connect = || -> Box<dyn MessageStream> {
        let tcp_stream = linux_server::connect(addr).expect("couldn't connect to server");
        new_tls_client_stream(tcp_stream, client_config.clone())
    };

    benchmark_wrapper(TEST_SIZES, "Local TCP TLS (rustls) Message Exchange", c, tls_connect);
    handshake_wrapper("Local TCP TLS (rustls) Setup", c, tls_connect);

    let mut stream = tls_connect();
    stream.send_message(control::EXIT);
    server_handle.join().unwrap();
}
/// Message shown when a VM leg cannot reach its server.
const VM_CONNECT_HELP: &str = "Couldn't connect to VM. Make sure the VM is running with:\n\
     ./oak_benchmarks/linux_vm/run_vm.sh --image=<path> --port=5000 --port=5001 --port=5002 --headless";

fn plaintext_vm_tcp_benchmark(c: &mut Criterion) {
    let addr = get_vm_addr("plaintext", DEFAULT_PLAINTEXT_PORT);
    println!("Connecting to VM at {} for plaintext benchmark", addr);

    let connect = || -> Box<dyn MessageStream> {
        Box::new(linux_server::connect(addr).expect(VM_CONNECT_HELP))
    };

    benchmark_wrapper(TEST_SIZES, "VM TCP Plaintext Message Exchange", c, connect);
    handshake_wrapper("VM TCP Plaintext Setup", c, connect);
}

fn new_noise_client_stream(addr: SocketAddr) -> Box<dyn MessageStream> {
    let tcp_stream = linux_server::connect(addr).expect("couldn't connect to server");
    Box::new(NoiseMessageStream::new_client(tcp_stream))
}

fn noise_vm_tcp_benchmark(c: &mut Criterion) {
    let addr = get_vm_addr("noise", DEFAULT_NOISE_PORT);
    println!("Connecting to VM at {} for noise benchmark", addr);

    benchmark_wrapper(TEST_SIZES, "VM TCP Noise Message Exchange", c, || {
        new_noise_client_stream(addr)
    });
    handshake_wrapper("VM TCP Noise Setup", c, || new_noise_client_stream(addr));
}

fn tls_vm_tcp_benchmark(c: &mut Criterion) {
    let addr = get_vm_addr("tls", DEFAULT_TLS_PORT);
    println!("Connecting to VM at {} for the TLS benchmark", addr);

    init_rustls();
    let (certs, _key) = load_certs_and_key();

    let mut root_store = rustls::RootCertStore::empty();
    root_store.add(certs[0].clone()).unwrap();
    let client_config = tls_client_config(root_store);

    let tls_connect = || -> Box<dyn MessageStream> {
        let tcp_stream = linux_server::connect(addr).expect(VM_CONNECT_HELP);
        new_tls_client_stream(tcp_stream, client_config.clone())
    };

    benchmark_wrapper(TEST_SIZES, "VM TCP TLS (rustls) Message Exchange", c, tls_connect);
    handshake_wrapper("VM TCP TLS (rustls) Setup", c, tls_connect);
}

fn plaintext_rk_benchmark(c: &mut Criterion) {
    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (guest_instance, oak_client_channel) =
        rt.block_on(async { start_rk_enclave_server(b"plaintext").await });

    benchmark_wrapper(TEST_SIZES, "RK Plaintext Message Exchange", c, || {
        Box::new(OakClientChannelMessageStream::new(&oak_client_channel))
    });
    // The plaintext enclave app serves every message over one channel, so this
    // only measures wrapping an existing handle -- there is no handshake to
    // pay for. It is the floor against which the Noise setup cost is read.
    handshake_wrapper("RK Plaintext Setup", c, || {
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
    handshake_wrapper("RK Noise Setup", c, || {
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
    tls_local_tcp_benchmark,
    plaintext_vm_tcp_benchmark,
    noise_vm_tcp_benchmark,
    tls_vm_tcp_benchmark
);
criterion_main!(benches);
