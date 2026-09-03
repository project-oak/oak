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

//! Measures where the time goes during session establishment, per leg.
//!
//! # Why this exists
//!
//! The evaluation plan asks for handshake latency "decomposed into evidence
//! transfer, DICE chain verification, Noise handshake, and binding
//! verification". Until now the crate could report only the *total*: the
//! criterion `Setup` groups in `benchmark.rs` time a whole `connect` plus
//! handshake and nothing finer, and the breakdown existed only as an analytic
//! model built from the P-256 primitive costs in `p256_cost.rs`. A model that
//! predicts 1302 µs against a measured 1423 µs is a good model, but it is not a
//! measurement, and a figure built from it has to be labelled as modelled.
//!
//! This binary measures it instead, without instrumenting `oak_session`. Every
//! boundary it times is one the harness already owns -- see
//! [`ClientNoiseMessageStream::new_client_with_config_traced`] for exactly what
//! each segment does and does not contain. The fine split *within* a segment,
//! for instance how much of the attestation ingest is the two P-256
//! verifications, remains modelled, and `p256_cost.rs` remains the right way to
//! estimate it.
//!
//! # What is comparable with what
//!
//! Four legs, all over loopback TCP so that the transport is identical and the
//! difference between them is protocol work:
//!
//! - `plaintext`: connect only. There is no handshake, so this is the floor
//!   that the other three should be read against.
//! - `noise`: unattested NoiseNN. Still performs the attestation exchange, with
//!   empty evidence, so it has the same number of round trips as the attested
//!   leg and the same segment labels.
//! - `noise-attested`: the same session with a software-rooted DICE chain and
//!   real client-side verification. The difference from `noise`, segment by
//!   segment, is what attestation costs.
//! - `tls`: rustls 1.3, full handshake (resumption disabled). Reported as two
//!   segments, `connect` and `handshake`, because rustls does not expose its
//!   own flights to a caller; `complete_io` is the whole exchange. That is
//!   coarser than the Noise legs and the output says so rather than inventing
//!   sub-segments.
//!
//! # An honest reading of `exchange`
//!
//! On loopback the `exchange` segment is not network time. It is the peer's
//! processing plus two context switches, and for the attested leg the server's
//! evidence assembly lands in it. Do not present it as a network cost, and do
//! not subtract it to get "protocol time": on a real link it would grow by the
//! RTT and shrink by nothing.
//!
//! # Output
//!
//! One row per segment per repetition, so that the raw data supports any
//! statistic the paper wants rather than only the one computed here:
//!
//! ```text
//! config,run,phase,work,us
//! ```
//!
//! A median table is printed to stderr for reading at the terminal. The CSV is
//! the artifact.

use std::{
    io::Write,
    net::{SocketAddr, TcpStream},
    sync::Arc,
    time::{Duration, Instant},
};

use clap::Parser;
use crypto_channel_attestation::{ServerAttestationMaterial, client_session_config};
use linux_server::{SETUP_SETTLE, init_rustls, load_certs_and_key, spin_for};
use message_stream_client::{
    BufferedStream, HandshakeSegment, MessageStream, NoiseMessageStream, control,
    unattested_noise_nn_config,
};
use rustls::{ClientConfig, ServerConfig};
use rustls_pki_types::ServerName;

/// One measured segment, flattened for output.
struct Row {
    config: &'static str,
    run: usize,
    phase: &'static str,
    work: &'static str,
    micros: f64,
}

#[derive(Parser)]
#[command(about = "Measures the per-segment cost of session establishment")]
struct Args {
    /// Session establishments to measure per leg.
    ///
    /// The evaluation plan asks for N = 1000. The default is lower so that a
    /// developer running this by hand does not wait minutes for a sanity
    /// check; pass the plan's value for a run whose numbers are quoted.
    #[arg(long, default_value_t = 100)]
    repetitions: usize,

    /// Establishments to run and discard before measuring, per leg.
    ///
    /// The plan's ground rules ask for at least three. Ten is cheap here and
    /// covers first-touch of the verification stack's static data on the
    /// attested leg.
    ///
    /// Measured effect, so nobody credits it with more than it does: raising
    /// warm-up from 0 to 20 and pinning the allocator moved the attested leg's
    /// total by 1.6%, from 2850 µs to 2805 µs. Warm-up is worth having, but it
    /// is not where the cost of an attested establishment lives.
    #[arg(long, default_value_t = 10)]
    warmup: usize,

    /// Where to write the CSV. Standard output if absent.
    #[arg(long)]
    output: Option<String>,
}

fn main() {
    let args = Args::parse();
    init_rustls();

    let mut rows = Vec::new();
    measure_plaintext(&args, &mut rows);
    measure_noise("noise", &args, &mut rows, None);
    measure_noise("noise-attested", &args, &mut rows, Some(()));
    measure_tls(&args, &mut rows);

    write_csv(&args.output, &rows);
    summarise(&rows);
}

/// Whether a given establishment is being measured or discarded.
///
/// Warm-up iterations run the identical code path -- the only difference is
/// that their segments are not recorded -- so a warm-up that differs from a
/// measured run is impossible by construction.
fn is_warmup(index: usize, args: &Args) -> bool {
    index < args.warmup
}

fn total_iterations(args: &Args) -> usize {
    args.warmup + args.repetitions
}

/// Connect, with no handshake on top: the floor for the other three legs.
fn measure_plaintext(args: &Args, rows: &mut Vec<Row>) {
    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(|tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            Box::new(BufferedStream::new(tcp_stream))
        }),
    );

    for i in 0..total_iterations(args) {
        let start = Instant::now();
        let tcp_stream = linux_server::connect(addr).expect("couldn't connect to server");
        let connect = start.elapsed();
        if !is_warmup(i, args) {
            rows.push(Row {
                config: "plaintext",
                run: i - args.warmup,
                phase: "none",
                work: "connect",
                micros: micros(connect),
            });
        }

        let mut stream = BufferedStream::new(tcp_stream);
        close(&mut stream);
    }

    shutdown(addr, |s| Box::new(BufferedStream::new(s)), server_handle);
}

/// A Noise session, attested or not, decomposed by session-protocol message.
///
/// The two legs share this function because they differ only in the two
/// `SessionConfig`s. Running them through separate code would leave open the
/// question of whether the difference between them is attestation or the
/// harness.
fn measure_noise(
    config_name: &'static str,
    args: &Args,
    rows: &mut Vec<Row>,
    attested: Option<()>,
) {
    let material = attested.map(|()| {
        Arc::new(
            ServerAttestationMaterial::generate().expect("generating server attestation material"),
        )
    });

    let server_material = material.clone();
    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(move |tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            let session_config = match &server_material {
                Some(m) => m.session_config(),
                None => unattested_noise_nn_config(),
            };
            Box::new(NoiseMessageStream::new_server_with_config(
                BufferedStream::new(tcp_stream),
                session_config,
            ))
        }),
    );

    for i in 0..total_iterations(args) {
        let run = i.saturating_sub(args.warmup);
        let measured = !is_warmup(i, args);

        let start = Instant::now();
        let tcp_stream = linux_server::connect(addr).expect("couldn't connect to server");
        let connect = start.elapsed();
        if measured {
            rows.push(Row {
                config: config_name,
                run,
                phase: "none",
                work: "connect",
                micros: micros(connect),
            });
        }

        let session_config =
            if material.is_some() { client_session_config() } else { unattested_noise_nn_config() };

        let mut trace: Vec<HandshakeSegment> = Vec::new();
        let mut stream = NoiseMessageStream::new_client_with_config_traced(
            BufferedStream::new(tcp_stream),
            session_config,
            &mut trace,
        );
        if measured {
            for segment in &trace {
                rows.push(Row {
                    config: config_name,
                    run,
                    phase: segment.phase.as_str(),
                    work: segment.work.as_str(),
                    micros: micros(segment.duration),
                });
            }
        }

        close(&mut stream);
    }

    let noise_client = {
        let material = material.clone();
        move |s: TcpStream| -> Box<dyn MessageStream> {
            let session_config = match &material {
                Some(_) => client_session_config(),
                None => unattested_noise_nn_config(),
            };
            Box::new(NoiseMessageStream::new_client_with_config(
                BufferedStream::new(s),
                session_config,
            ))
        }
    };
    shutdown(addr, noise_client, server_handle);
}

/// rustls, reported as connect plus one opaque handshake.
///
/// rustls drives the whole exchange inside `complete_io` and does not surface
/// the individual flights, so there is nothing finer to time from outside it.
/// Splitting it would mean either reimplementing the state machine or reading
/// rustls internals, and both would measure the harness rather than TLS.
fn measure_tls(args: &Args, rows: &mut Vec<Row>) {
    let (certs, key) = load_certs_and_key();
    let server_config = Arc::new(
        ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(certs.clone(), key)
            .expect("bad certificate/key"),
    );

    let (addr, server_handle) = linux_server::start_tcp_server(
        "127.0.0.1:0",
        Arc::new(move |tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            let conn = rustls::ServerConnection::new(server_config.clone()).unwrap();
            Box::new(BufferedStream::new(rustls::StreamOwned::new(conn, tcp_stream)))
        }),
    );

    let mut root_store = rustls::RootCertStore::empty();
    root_store.add(certs[0].clone()).unwrap();
    let mut client_config =
        ClientConfig::builder().with_root_certificates(root_store).with_no_client_auth();
    // Same reason as `benchmark.rs`: a resumed handshake sends no certificate
    // and generates no signature, so it is not the exchange the Noise legs
    // perform. Asserted below rather than trusted.
    client_config.resumption = rustls::client::Resumption::disabled();
    let client_config = Arc::new(client_config);

    for i in 0..total_iterations(args) {
        let run = i.saturating_sub(args.warmup);
        let measured = !is_warmup(i, args);

        let start = Instant::now();
        let tcp_stream = linux_server::connect(addr).expect("couldn't connect to server");
        let connect = start.elapsed();

        let start = Instant::now();
        let mut stream = tls_stream(tcp_stream, client_config.clone());
        let handshake = start.elapsed();

        if measured {
            rows.push(Row {
                config: "tls",
                run,
                phase: "none",
                work: "connect",
                micros: micros(connect),
            });
            rows.push(Row {
                config: "tls",
                run,
                phase: "tls",
                work: "handshake",
                micros: micros(handshake),
            });
        }

        close(&mut stream);
    }

    let tls_client = move |s: TcpStream| -> Box<dyn MessageStream> {
        Box::new(tls_stream(s, client_config.clone()))
    };
    shutdown(addr, tls_client, server_handle);
}

fn tls_stream(
    tcp_stream: TcpStream,
    client_config: Arc<ClientConfig>,
) -> BufferedStream<rustls::StreamOwned<rustls::ClientConnection, TcpStream>> {
    let server_name = ServerName::try_from("localhost").unwrap().to_owned();
    let conn = rustls::ClientConnection::new(client_config, server_name).unwrap();
    let mut stream = rustls::StreamOwned::new(conn, tcp_stream);
    stream.conn.complete_io(&mut stream.sock).expect("tls handshake failed");
    assert_eq!(
        stream.conn.handshake_kind(),
        Some(rustls::HandshakeKind::Full),
        "the tls leg must perform a full handshake, otherwise it is not measuring \
         the same exchange as the noise legs"
    );
    BufferedStream::new(stream)
}

/// Ends one channel and waits out the teardown, both untimed.
///
/// The server serves one channel at a time, so the close is required; the wait
/// is required because a connect issued immediately after a teardown is
/// measurably slower. See [`SETUP_SETTLE`].
fn close(stream: &mut dyn MessageStream) {
    stream.send_message(control::CLOSE);
    stream.read_message();
    spin_for(SETUP_SETTLE);
}

/// Stops a server and joins its thread.
fn shutdown(
    addr: SocketAddr,
    connect: impl Fn(TcpStream) -> Box<dyn MessageStream>,
    handle: std::thread::JoinHandle<()>,
) {
    let tcp_stream = linux_server::connect(addr).expect("couldn't connect to server");
    let mut stream = connect(tcp_stream);
    stream.send_message(control::EXIT);
    handle.join().unwrap();
}

fn micros(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e6
}

fn write_csv(output: &Option<String>, rows: &[Row]) {
    let mut out: Box<dyn Write> = match output {
        Some(path) => Box::new(std::fs::File::create(path).expect("creating output file")),
        None => Box::new(std::io::stdout()),
    };
    writeln!(out, "config,run,phase,work,us").unwrap();
    for row in rows {
        writeln!(out, "{},{},{},{},{:.3}", row.config, row.run, row.phase, row.work, row.micros)
            .unwrap();
    }
}

/// Prints per-segment medians, and the total each leg's segments sum to.
///
/// The totals are the cross-check that matters: the plan's sanity condition is
/// that the segments account for the whole establishment, and a sum that drifts
/// from the criterion `Setup` figure for the same leg means one of the two is
/// measuring something else.
fn summarise(rows: &[Row]) {
    let mut configs: Vec<&str> = Vec::new();
    for row in rows {
        if !configs.contains(&row.config) {
            configs.push(row.config);
        }
    }

    eprintln!();
    eprintln!("{:<16} {:<10} {:<10} {:>12}", "config", "phase", "work", "median us");
    for config in configs {
        let mut keys: Vec<(&str, &str)> = Vec::new();
        for row in rows.iter().filter(|r| r.config == config) {
            if !keys.contains(&(row.phase, row.work)) {
                keys.push((row.phase, row.work));
            }
        }
        let mut total = 0.0;
        for (phase, work) in keys {
            let mut values: Vec<f64> = rows
                .iter()
                .filter(|r| r.config == config && r.phase == phase && r.work == work)
                .map(|r| r.micros)
                .collect();
            let median = median(&mut values);
            total += median;
            eprintln!("{:<16} {:<10} {:<10} {:>12.1}", config, phase, work, median);
        }
        eprintln!("{:<16} {:<10} {:<10} {:>12.1}", config, "", "TOTAL", total);
    }
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = values.len();
    if n == 0 {
        return 0.0;
    }
    if n % 2 == 1 { values[n / 2] } else { (values[n / 2 - 1] + values[n / 2]) / 2.0 }
}
