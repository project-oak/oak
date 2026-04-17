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

use std::{
    fs::File,
    io::BufReader,
    net::{SocketAddr, TcpListener, TcpStream},
    sync::{Arc, Once},
    thread::{self, JoinHandle},
};

use message_stream_client::MessageStream;
use oak_file_utils::data_path;
use rustls_pki_types::{CertificateDer, PrivateKeyDer};

static INIT_RUSTLS: Once = Once::new();

pub fn init_rustls() {
    INIT_RUSTLS.call_once(|| {
        rustls::crypto::ring::default_provider()
            .install_default()
            .expect("failed to install rustls crypto provider");
    });
}

pub fn load_certs_and_key() -> (Vec<CertificateDer<'static>>, PrivateKeyDer<'static>) {
    let cert_path = data_path("oak_benchmarks/oak_paper/crypto_channel/certs.pem");
    let mut reader = BufReader::new(File::open(cert_path).expect("cannot open certs file"));
    let mut certs = Vec::new();
    let mut key = None;
    for item in rustls_pemfile::read_all(&mut reader) {
        match item.expect("pem error") {
            rustls_pemfile::Item::X509Certificate(cert) => certs.push(cert),
            rustls_pemfile::Item::Pkcs8Key(k) => key = Some(PrivateKeyDer::Pkcs8(k)),
            _ => {}
        }
    }
    (certs, key.expect("no key found"))
}

pub type ServerStreamCreator =
    Arc<dyn Fn(TcpStream) -> Box<dyn MessageStream> + Send + Sync + 'static>;

pub fn start_tcp_server(
    addr: &str,
    stream_creator: ServerStreamCreator,
) -> (SocketAddr, JoinHandle<()>) {
    let listener = TcpListener::bind(addr).expect("failed to bind server");
    let addr = listener.local_addr().expect("failed to get local address");
    let handle = thread::spawn(move || {
        loop {
            let (tcp_stream, _) = listener.accept().expect("failed to receive connection");
            let stream = &mut stream_creator(tcp_stream);

            let read_msg = stream.read_message();
            if read_msg == b"exit" {
                break;
            }
            stream.send_message(&read_msg);
        }
    });
    (addr, handle)
}
