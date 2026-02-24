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

use std::sync::Arc;

use clap::Parser;
use message_stream_client::NoiseMessageStream;
use rustls::ServerConfig;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value = "127.0.0.1:8080")]
    addr: String,

    #[arg(short, long, default_value = "plaintext")]
    mode: String,
}

fn main() {
    let args = Args::parse();

    let stream_creator: linux_server::ServerStreamCreator = match args.mode.as_str() {
        "plaintext" => Arc::new(|tcp_stream| Box::new(tcp_stream)),
        "noise" => Arc::new(|tcp_stream| Box::new(NoiseMessageStream::new_server(tcp_stream))),
        "boringssl" => {
            linux_server::init_rustls();
            let (certs, key) = linux_server::load_certs_and_key();
            let server_config = ServerConfig::builder()
                .with_no_client_auth()
                .with_single_cert(certs, key)
                .expect("bad certificate/key");
            let server_config = Arc::new(server_config);
            Arc::new(move |tcp_stream| {
                let conn = rustls::ServerConnection::new(server_config.clone()).unwrap();
                Box::new(rustls::StreamOwned::new(conn, tcp_stream))
            })
        }
        _ => panic!("unknown mode: {}", args.mode),
    };

    let (addr, handle) = linux_server::start_tcp_server(&args.addr, stream_creator);
    println!("Listening on {}", addr);
    handle.join().expect("server thread panicked");
}
