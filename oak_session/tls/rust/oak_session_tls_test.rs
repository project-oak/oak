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

use oak_session_tls::*;
use rustls_pki_types::{CertificateDer, PrivateKeyDer};
use tokio::sync::Mutex;

fn load_test_cert(path: &str) -> CertificateDer<'static> {
    utils::load_cert_der(std::io::BufReader::new(
        std::fs::File::open(path).expect("failed to open cert file"),
    ))
}

fn load_test_key(path: &str) -> PrivateKeyDer<'static> {
    utils::load_key_der(std::io::BufReader::new(
        std::fs::File::open(path).expect("failed to open key file"),
    ))
}

#[tokio::test]
async fn test_handshake() -> Result<(), Box<dyn std::error::Error>> {
    let pair = TestSessionPair::create(None);
    let mut server = AsyncServer::spawn(pair.server);

    let mut client = do_handshake(&mut server, pair.client).await;

    let msg = b"hello world";
    let encrypted = client.encrypt(msg)?;
    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    let msg2 = b"hello back";
    let encrypted2 = server.encrypt(msg2).await.unwrap();

    let decrypted2 =
        read_until_plaintext(&mut client, &mut server.from_server_tls_rx, encrypted2).await?;
    assert_eq!(decrypted2, msg2);

    Ok(())
}

async fn read_until_plaintext(
    client: &mut OakSessionTls,
    rx: &mut tokio::sync::mpsc::UnboundedReceiver<Vec<u8>>,
    initial_frame: Vec<u8>,
) -> Result<Vec<u8>, SessionError> {
    let mut all_plaintext = Vec::new();
    let mut current_frame = initial_frame;
    loop {
        let plaintext = client.decrypt(&current_frame)?;
        all_plaintext.extend(plaintext);
        if !all_plaintext.is_empty() {
            return Ok(all_plaintext);
        }
        current_frame = rx.recv().await.expect("channel closed");
    }
}

#[tokio::test]
async fn test_mtls_handshake() -> Result<(), Box<dyn std::error::Error>> {
    let client_cert = load_test_cert("oak_session/tls/testing/test_client.pem");
    let client_key = load_test_key("oak_session/tls/testing/test_client.key");

    let pair =
        TestSessionPair::create(Some(TlsIdentity { key_der: client_key, cert_der: client_cert }));
    let mut server = AsyncServer::spawn(pair.server);

    let mut client_session = do_handshake(&mut server, pair.client).await;

    let msg = b"mtls test";
    let encrypted = client_session.encrypt(msg)?;
    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    Ok(())
}

#[tokio::test]
async fn test_large_data_transfer() -> Result<(), Box<dyn std::error::Error>> {
    let pair = TestSessionPair::create(None);
    let mut server = AsyncServer::spawn(pair.server);

    let mut client = do_handshake(&mut server, pair.client).await;

    // Larger than one TLS record
    let msg = vec![0x42u8; 100 * 1024]; // 100 KB
    let encrypted = client.encrypt(&msg)?;
    assert!(!encrypted.is_empty());

    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    Ok(())
}

#[tokio::test]
async fn test_decrypt_invalid() -> Result<(), Box<dyn std::error::Error>> {
    let pair = TestSessionPair::create(None);
    let mut server = AsyncServer::spawn(pair.server);

    let mut client = do_handshake(&mut server, pair.client).await;

    let msg = b"hello";
    let encrypted = client.encrypt(msg)?;

    // Add extra garbage data to the end of the encrypted buffer.
    let mut malformed = encrypted.clone();
    malformed.extend_from_slice(b"garbage");

    let res = server.decrypt(malformed).await;

    // rustls will return a Tls error when it tries to parse the garbage.
    assert!(res.is_err());

    Ok(())
}

struct TestSessionPair {
    pub server: OakSessionTlsInitializer,
    pub client: OakSessionTlsInitializer,
}

impl TestSessionPair {
    fn create(client_identity: Option<TlsIdentity>) -> Self {
        let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
        let server_cert = load_test_cert("oak_session/tls/testing/test_server.pem");
        let server_key = load_test_key("oak_session/tls/testing/test_server.key");

        let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
            tls_identity: TlsIdentity { key_der: server_key, cert_der: server_cert },
            client_trust_anchor_der: client_identity.as_ref().map(|_| ca_cert.clone()),
        })
        .expect("failed to create server context");

        let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
            server_trust_anchor_der: Some(ca_cert),
            tls_identity: client_identity,
        })
        .expect("failed to create client context");

        let server = server_ctx.new_session().expect("failed to create server session");
        let client = client_ctx.new_session().expect("failed to create client session");

        Self { server, client }
    }
}

/// A helper struct that runs an `OakSessionTls` server in a background task for
/// testing.
///
/// It uses two sets of channels:
/// 1. The "network pipe" channels (`to_server_tls_tx`, `from_server_tls_rx`)
///    which carry encrypted TLS frames. These mimic the actual communication
///    channel.
/// 2. The "control" channels (`to_server_enc_tx`, `from_server_plaintext_rx`)
///    which allow the test to interact with the server's plaintext side (e.g.,
///    asking it to encrypt data or receiving decrypted data).
struct AsyncServer {
    /// Channel for sending TLS-encrypted data to the server (mimicking network
    /// input).
    pub to_server_tls_tx: tokio::sync::mpsc::UnboundedSender<Vec<u8>>,
    /// Channel for receiving TLS-encrypted data from the server (mimicking
    /// network output).
    pub from_server_tls_rx: tokio::sync::mpsc::UnboundedReceiver<Vec<u8>>,
    /// Channel for receiving decrypted plaintext or errors from the server.
    pub from_server_plaintext_rx: tokio::sync::mpsc::UnboundedReceiver<Result<Vec<u8>, String>>,
    /// Channel for sending plaintext to the server to be encrypted.
    pub to_server_enc_tx: tokio::sync::mpsc::UnboundedSender<Vec<u8>>,
}

impl AsyncServer {
    fn spawn(init: OakSessionTlsInitializer) -> Self {
        let (to_server_tls_tx, mut to_server_tls_rx) =
            tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();
        let (from_server_tls_tx, from_server_tls_rx) =
            tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();
        let (from_server_plaintext_tx, from_server_plaintext_rx) =
            tokio::sync::mpsc::unbounded_channel::<Result<Vec<u8>, String>>();
        let (to_server_enc_tx, mut to_server_enc_rx) =
            tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();

        tokio::spawn(async move {
            let (mut server, initial_data) =
                handshake_loop(init, &from_server_tls_tx, &mut to_server_tls_rx).await;

            if !initial_data.is_empty() {
                from_server_plaintext_tx
                    .send(Ok(initial_data))
                    .expect("failed to send initial data");
            }

            loop {
                tokio::select! {
                    Some(plaintext) = to_server_enc_rx.recv() => {
                        match server.encrypt(&plaintext) {
                            Ok(encrypted) => {
                                from_server_tls_tx.send(encrypted).expect("failed to send TLS frame");
                            }
                            Err(e) => {
                                from_server_plaintext_tx.send(Err(format!("{:?}", e))).expect("failed to send error");
                            }
                        }
                    }
                    Some(frame) = to_server_tls_rx.recv() => {
                        match server.decrypt(&frame) {
                            Ok(decrypted) => {
                                if !decrypted.is_empty() {
                                    from_server_plaintext_tx.send(Ok(decrypted)).expect("failed to send decrypted plaintext");
                                }
                            }
                            Err(e) => {
                                from_server_plaintext_tx.send(Err(format!("{:?}", e))).expect("failed to send error");
                            }
                        }
                    }
                }
            }
        });

        Self { to_server_tls_tx, from_server_tls_rx, from_server_plaintext_rx, to_server_enc_tx }
    }

    async fn decrypt(&mut self, frame: Vec<u8>) -> Result<Vec<u8>, String> {
        self.to_server_tls_tx.send(frame).expect("failed to send TLS frame");
        self.from_server_plaintext_rx.recv().await.expect("failed to receive plaintext")
    }

    async fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>, String> {
        self.to_server_enc_tx.send(plaintext.to_vec()).expect("failed to send plaintext");
        self.from_server_tls_rx.recv().await.ok_or("server closed".to_string())
    }
}

async fn do_handshake(server: &mut AsyncServer, client: OakSessionTlsInitializer) -> OakSessionTls {
    let (session, initial_data) =
        handshake_loop(client, &server.to_server_tls_tx, &mut server.from_server_tls_rx).await;

    if !initial_data.is_empty() {
        println!("Client: Received {} bytes of initial data during handshake", initial_data.len());
    }
    session
}

// A helper to wrap the handshake loop, which is used by both the client and
// server tests. It takes care of
async fn handshake_loop(
    init: OakSessionTlsInitializer,
    tx: &tokio::sync::mpsc::UnboundedSender<Vec<u8>>,
    rx: &mut tokio::sync::mpsc::UnboundedReceiver<Vec<u8>>,
) -> (OakSessionTls, Vec<u8>) {
    // We wrap the receiver in a Mutex so that the async closure can safely capture
    // it. In a real application, you might have a more direct way to manage
    // this.
    let rx = Arc::new(Mutex::new(rx));
    let mut sender = |frame| {
        let tx = tx.clone();
        async move {
            tx.send(frame).map_err(|_| {
                InitializationError::Io(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "send failed",
                ))
            })
        }
    };
    let mut receiver = move || {
        let rx = rx.clone();
        async move { Ok(rx.lock().await.recv().await) }
    };

    init.handshake(&mut sender, &mut receiver).await.expect("handshake failed")
}
