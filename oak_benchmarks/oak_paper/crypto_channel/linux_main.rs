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

//! Multi-port TCP server for crypto channel benchmarks.
//!
//! Serves all three protocols (plaintext, noise, boringssl) simultaneously
//! on different ports, allowing benchmarks to run without restarting the VM.

use std::sync::Arc;

use clap::Parser;
use message_stream_client::NoiseMessageStream;
use rustls::ServerConfig;

#[derive(Parser, Debug)]
#[command(author, version, about = "Multi-port TCP server for crypto channel benchmarks")]
struct Args {
    /// Host address to bind to.
    #[arg(long, default_value = "0.0.0.0")]
    host: String,

    /// Port for plaintext protocol (0 to disable).
    #[arg(long, default_value_t = linux_server::DEFAULT_PLAINTEXT_PORT)]
    plaintext_port: u16,

    /// Port for Noise protocol (0 to disable).
    #[arg(long, default_value_t = linux_server::DEFAULT_NOISE_PORT)]
    noise_port: u16,

    /// Port for BoringSSL/TLS protocol (0 to disable).
    #[arg(long, default_value_t = linux_server::DEFAULT_BORINGSSL_PORT)]
    boringssl_port: u16,
}

fn main() {
    let args = Args::parse();

    let mut handles = Vec::new();

    // Start plaintext server.
    if args.plaintext_port != 0 {
        let addr = format!("{}:{}", args.host, args.plaintext_port);
        let stream_creator: linux_server::ServerStreamCreator =
            Arc::new(|tcp_stream| Box::new(tcp_stream));
        let (bound_addr, handle) = linux_server::start_tcp_server(&addr, stream_creator);
        println!("Plaintext server listening on {}", bound_addr);
        handles.push(("plaintext", handle));
    }

    // Start Noise server.
    if args.noise_port != 0 {
        let addr = format!("{}:{}", args.host, args.noise_port);
        let stream_creator: linux_server::ServerStreamCreator =
            Arc::new(|tcp_stream| Box::new(NoiseMessageStream::new_server(tcp_stream)));
        let (bound_addr, handle) = linux_server::start_tcp_server(&addr, stream_creator);
        println!("Noise server listening on {}", bound_addr);
        handles.push(("noise", handle));
    }

    // Start BoringSSL/TLS server.
    if args.boringssl_port != 0 {
        // Try to load certs - this may fail if running outside Bazel (e.g., in a VM).
        match std::panic::catch_unwind(|| {
            linux_server::init_rustls();
            linux_server::load_certs_and_key()
        }) {
            Ok((certs, key)) => {
                let server_config = ServerConfig::builder()
                    .with_no_client_auth()
                    .with_single_cert(certs, key)
                    .expect("bad certificate/key");
                let server_config = Arc::new(server_config);

                let addr = format!("{}:{}", args.host, args.boringssl_port);
                let stream_creator: linux_server::ServerStreamCreator =
                    Arc::new(move |tcp_stream| {
                        let conn = rustls::ServerConnection::new(server_config.clone()).unwrap();
                        Box::new(rustls::StreamOwned::new(conn, tcp_stream))
                    });
                let (bound_addr, handle) = linux_server::start_tcp_server(&addr, stream_creator);
                println!("BoringSSL server listening on {}", bound_addr);
                handles.push(("boringssl", handle));
            }
            Err(_) => {
                eprintln!(
                    "Warning: Could not load TLS certificates (runfiles not available). \
                     BoringSSL server disabled."
                );
            }
        }
    }

    if handles.is_empty() {
        eprintln!("Error: No servers enabled. Set at least one port to non-zero.");
        std::process::exit(1);
    }

    println!("\nAll servers started. Press Ctrl+C to stop.");

    // Wait for all server threads.
    for (name, handle) in handles {
        handle.join().unwrap_or_else(|_| eprintln!("{} server panicked", name));
    }
}
