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

pub const DEFAULT_PLAINTEXT_PORT: u16 = 5000;
pub const DEFAULT_NOISE_PORT: u16 = 5001;

/// Port for the TLS leg.
///
/// The TLS implementation is rustls with the `ring` provider, installed by
/// [`init_rustls`]. This constant and everything else on this leg used to be
/// named after BoringSSL, which was never what the code linked. BoringSSL is
/// a dependency of this repository -- see the `boringssl` bazel_dep in
/// MODULE.bazel, used by `cc/crypto/hpke` and `oak_session/tls` -- so the old
/// name was plausible enough to be repeated in a paper without anyone
/// checking it against the build graph.
pub const DEFAULT_TLS_PORT: u16 = 5002;

static INIT_RUSTLS: Once = Once::new();

/// Installs the process-wide rustls crypto provider.
///
/// Idempotent, because rustls rejects a second install and the benchmarks
/// reach this from several entry points.
pub fn init_rustls() {
    INIT_RUSTLS.call_once(|| {
        rustls::crypto::ring::default_provider()
            .install_default()
            .expect("failed to install rustls crypto provider");
    });
}

pub fn load_certs_and_key() -> (Vec<CertificateDer<'static>>, PrivateKeyDer<'static>) {
    // Try runfiles path first (when running under Bazel), then fallback to VM path.
    let cert_path =
        std::panic::catch_unwind(|| data_path("oak_benchmarks/oak_paper/crypto_channel/certs.pem"))
            .ok()
            .filter(|p| std::path::Path::new(p).exists())
            .unwrap_or_else(|| "/opt/app/certs.pem".into());

    let mut reader = BufReader::new(File::open(&cert_path).expect("cannot open certs file"));
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
