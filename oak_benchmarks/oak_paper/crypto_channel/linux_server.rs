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

use message_stream_client::{MessageStream, control};
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

/// Disables Nagle's algorithm on a benchmark socket.
///
/// Every leg frames a message as a 4-byte length followed by the body, which
/// is two `write` calls. With Nagle enabled the second write is held back
/// while the first is unacknowledged, and the peer -- blocked in `read_exact`
/// waiting for the body it has not been given -- has nothing to piggyback an
/// acknowledgement on, so it waits out its delayed-ACK timer. On Linux that
/// timer is 40 ms, and the exchange pays it.
///
/// This is not a micro-optimisation. Local TCP, 50 samples per point:
///
/// ```text
///                            Nagle      TCP_NODELAY     change
///   Noise  Message Exchange  22.83 ms      13.58 us    -99.94%
///   Noise  Setup             91.68 ms     529.81 us    -99.42%
///   TLS    Message Exchange  52.66 us      19.56 us    -62.9%
///   Plaintext (both groups)   no material change
/// ```
///
/// Every leg is hurt, but not equally, which is what makes leaving it on so
/// damaging: the ranking inverts. With Nagle on, Noise looks 433x slower than
/// rustls; with it off, Noise is 1.4x faster. A benchmark that decides the
/// paper's central comparison on the kernel's delayed-ACK timer is not
/// measuring the protocols at all.
///
/// Plaintext escapes because its connections carry one exchange and nothing
/// precedes it, so there is never an unacknowledged segment to trigger the
/// hold. Why rustls suffered less than Noise is **not** established. An earlier
/// version of this comment said rustls coalesces a record into a single write;
/// that is wrong. `rustls::StreamOwned::write` forms a record and then calls
/// `complete_io`, so each of the two framing writes produced its own record
/// *and* its own socket write, exactly as the Noise leg did.
///
/// Every RPC stack that carries small messages sets this -- gRPC, HTTP/2 and
/// Thrift all do -- so it is also what the systems being modelled would do.
///
/// `message_stream.rs` now frames the length and body into one write, which
/// removes the second record and helps the Restricted Kernel channel too.
/// Disabling Nagle remains necessary and is independently justified.
fn disable_nagle(tcp_stream: &TcpStream) {
    tcp_stream.set_nodelay(true).expect("failed to set TCP_NODELAY");
}

/// Connects to a benchmark server with Nagle disabled.
///
/// Use this rather than [`TcpStream::connect`] directly, so that no leg is
/// accidentally measured with Nagle still on. See [`disable_nagle`].
pub fn connect(addr: SocketAddr) -> std::io::Result<TcpStream> {
    let tcp_stream = TcpStream::connect(addr)?;
    disable_nagle(&tcp_stream);
    Ok(tcp_stream)
}

/// Runs an echo server on a background thread until a client sends
/// [`control::EXIT`].
///
/// Each accepted connection is served until the client sends
/// [`control::CLOSE`] or simply goes away, at which point the server returns
/// to `accept`. Serving more than one message per connection is what lets a
/// benchmark hold a channel open across a whole measurement, so that what it
/// times is the exchange rather than the exchange plus a connect.
///
/// A client that disconnects without saying [`control::CLOSE`] is tolerated.
/// It has to be: the server outlives every client, so a panic here would be
/// reported much later, against whichever leg happened to run next.
///
/// One connection is served at a time, deliberately. These benchmarks measure
/// latency on an idle path; a concurrent server would add scheduling noise
/// and measure something else. It does mean a second client blocks in the
/// listen backlog until the first is done.
pub fn start_tcp_server(
    addr: &str,
    stream_creator: ServerStreamCreator,
) -> (SocketAddr, JoinHandle<()>) {
    let listener = TcpListener::bind(addr).expect("failed to bind server");
    let addr = listener.local_addr().expect("failed to get local address");
    let handle = thread::spawn(move || {
        'accept: loop {
            let (tcp_stream, _) = listener.accept().expect("failed to receive connection");
            // The server replies with the same two-write framing, so it stalls
            // the client the same way if this is left out.
            disable_nagle(&tcp_stream);
            let stream = &mut stream_creator(tcp_stream);

            while let Some(read_msg) = stream.try_read_message() {
                if read_msg == control::EXIT {
                    break 'accept;
                }
                stream.send_message(&read_msg);
                if read_msg == control::CLOSE {
                    break;
                }
            }
        }
    });
    (addr, handle)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use googletest::prelude::*;

    use super::*;

    /// Nagle costs about 40 ms per exchange on these legs and inverts the
    /// Noise-versus-rustls ranking, so it is worth a test rather than a
    /// comment. See [`disable_nagle`].
    #[googletest::test]
    fn connect_disables_nagle() {
        let listener = TcpListener::bind("127.0.0.1:0").expect("failed to bind");
        let addr = listener.local_addr().expect("failed to get local address");

        let client = connect(addr).expect("failed to connect");

        expect_that!(client.nodelay().expect("failed to read TCP_NODELAY"), eq(true));
    }

    /// The accepted side frames its reply the same way, so it stalls the
    /// client identically if Nagle is left on there.
    #[googletest::test]
    fn served_connections_disable_nagle() {
        // Reports what the server saw, since the accepted socket is consumed
        // by the stream creator and cannot be inspected from outside.
        let (nodelay_tx, nodelay_rx) = std::sync::mpsc::channel();
        let (addr, handle) = start_tcp_server(
            "127.0.0.1:0",
            Arc::new(move |tcp_stream: TcpStream| -> Box<dyn MessageStream> {
                nodelay_tx.send(tcp_stream.nodelay().expect("failed to read TCP_NODELAY")).ok();
                Box::new(tcp_stream)
            }),
        );

        let mut client = connect(addr).expect("failed to connect");
        client.send_message(control::EXIT);
        handle.join().expect("server panicked");

        expect_that!(nodelay_rx.recv(), ok(eq(true)));
    }

    /// Counts accepted connections, so that a regression to one connection
    /// per message is a test failure rather than a slow benchmark.
    fn counting_echo_server() -> (SocketAddr, JoinHandle<()>, Arc<AtomicUsize>) {
        let accepted = Arc::new(AtomicUsize::new(0));
        let counter = accepted.clone();
        let (addr, handle) = start_tcp_server(
            "127.0.0.1:0",
            Arc::new(move |tcp_stream: TcpStream| -> Box<dyn MessageStream> {
                counter.fetch_add(1, Ordering::SeqCst);
                Box::new(tcp_stream)
            }),
        );
        (addr, handle, accepted)
    }

    /// The point of the change: a channel survives more than one exchange.
    ///
    /// Without this the message-exchange benchmark cannot hold a channel open,
    /// and every iteration pays a connect that the reported figure excludes
    /// but the machine does not.
    #[googletest::test]
    fn serves_many_messages_on_one_connection() {
        let (addr, handle, accepted) = counting_echo_server();

        let mut client = connect(addr).expect("failed to connect");
        for i in 0..5u8 {
            client.send_message(&[i]);
            expect_that!(client.read_message(), eq(&vec![i]));
        }
        client.send_message(control::EXIT);
        handle.join().expect("server panicked");

        expect_that!(accepted.load(Ordering::SeqCst), eq(1));
    }

    /// `CLOSE` is acknowledged and returns the server to `accept`, so the
    /// handshake benchmark can measure setup repeatedly against one server.
    #[googletest::test]
    fn close_acknowledges_and_frees_the_server() {
        let (addr, handle, accepted) = counting_echo_server();

        for _ in 0..3 {
            let mut client = connect(addr).expect("failed to connect");
            client.send_message(control::CLOSE);
            expect_that!(client.read_message(), eq(&control::CLOSE.to_vec()));
        }

        let mut client = connect(addr).expect("failed to connect");
        client.send_message(control::EXIT);
        handle.join().expect("server panicked");

        expect_that!(accepted.load(Ordering::SeqCst), eq(4));
    }

    /// A client that drops its socket without saying [`control::CLOSE`] must
    /// not take the server with it.
    ///
    /// This is not hypothetical. The VM readiness probe connects, exchanges
    /// one message to confirm the guest is serving, and hangs up; an earlier
    /// version of this loop panicked the plaintext server thread at that
    /// point, and the leg then failed several minutes later for no visible
    /// reason.
    #[googletest::test]
    fn survives_a_client_that_disconnects() {
        let (addr, handle, accepted) = counting_echo_server();

        {
            let mut client = connect(addr).expect("failed to connect");
            client.send_message(&[7u8]);
            expect_that!(client.read_message(), eq(&vec![7u8]));
            // Dropped without CLOSE, exactly as the readiness probe does.
        }

        // The server is still there and still serving.
        let mut client = connect(addr).expect("failed to connect");
        client.send_message(&[9u8]);
        expect_that!(client.read_message(), eq(&vec![9u8]));
        client.send_message(control::EXIT);
        handle.join().expect("server panicked");

        expect_that!(accepted.load(Ordering::SeqCst), eq(2));
    }
}
