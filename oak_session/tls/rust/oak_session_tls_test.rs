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
    let mut server = AsyncServer::spawn(pair.server_ctx);

    let mut client = do_handshake(&mut server, &pair.client_ctx).await;

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
    let mut server = AsyncServer::spawn(pair.server_ctx);

    let mut client_session = do_handshake(&mut server, &pair.client_ctx).await;

    let msg = b"mtls test";
    let encrypted = client_session.encrypt(msg)?;
    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    Ok(())
}

#[tokio::test]
async fn test_large_data_transfer() -> Result<(), Box<dyn std::error::Error>> {
    let pair = TestSessionPair::create(None);
    let mut server = AsyncServer::spawn(pair.server_ctx);

    let mut client = do_handshake(&mut server, &pair.client_ctx).await;

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
    let mut server = AsyncServer::spawn(pair.server_ctx);

    let mut client = do_handshake(&mut server, &pair.client_ctx).await;

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

#[tokio::test]
async fn test_certificate_rotation_works() -> Result<(), Box<dyn std::error::Error>> {
    let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
    let server_cert = load_test_cert("oak_session/tls/testing/test_server.pem");
    let server_key = load_test_key("oak_session/tls/testing/test_server.key");

    let untrusted_cert = load_test_cert("oak_session/tls/testing/test_untrusted.pem");
    let untrusted_key = load_test_key("oak_session/tls/testing/test_untrusted.key");

    let current_identity =
        Arc::new(std::sync::Mutex::new(TlsIdentity { key_der: server_key, cert_der: server_cert }));

    let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: Box::new({
            let current = current_identity.clone();
            move || {
                let id = current.lock().unwrap();
                Ok(TlsIdentity { key_der: id.key_der.clone_key(), cert_der: id.cert_der.clone() })
            }
        }),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    })
    .expect("failed to create server context");

    let client_ctx1 = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(
            ca_cert.clone(),
        )),
        tls_identity_provider: None,
        custom_cert_verifier: None,
        expected_server_name: None,
    })
    .expect("failed to create client context");

    // First session: should succeed with the trusted cert
    {
        let mut server1 = server_ctx.new_session()?;
        let mut client1 = client_ctx1.new_session()?;

        let frame = client1.get_tls_frame()?;
        let _ = server1.put_tls_frame(&frame)?;
        let frame = server1.get_tls_frame()?;
        let result = client1.put_tls_frame(&frame);

        assert!(result.is_ok(), "Client should accept the trusted certificate");
    }

    // Rotate certificate to untrusted one
    {
        let mut id = current_identity.lock().unwrap();
        id.key_der = untrusted_key;
        id.cert_der = untrusted_cert;
    }

    let client_ctx2 = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(ca_cert)),
        tls_identity_provider: None,
        custom_cert_verifier: None,
        expected_server_name: None,
    })
    .expect("failed to create second client context");

    // Second session: should fail during handshake
    {
        let mut server2 = server_ctx.new_session()?;
        let mut client2 = client_ctx2.new_session()?;

        let frame = client2.get_tls_frame()?;
        let _ = server2.put_tls_frame(&frame)?;
        let frame = server2.get_tls_frame()?;

        // Client rejects the untrusted certificate emitted by the server's rotated
        // session
        let result = client2.put_tls_frame(&frame);
        assert!(result.is_err(), "Client should reject the untrusted certificate");
    }

    Ok(())
}

#[derive(Debug)]
struct MockVerifier {
    fail: bool,
    expect_inner_fail: Option<bool>,
}

impl CustomCertVerifier for MockVerifier {
    fn verify(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        verify_result: Result<(), &rustls::Error>,
    ) -> Result<(), String> {
        if let Some(expect_fail) = self.expect_inner_fail
            && expect_fail != verify_result.is_err()
        {
            return Err(format!(
                "Expected inner fail: {}, got: {}",
                expect_fail,
                verify_result.is_err()
            ));
        }
        if self.fail {
            return Err("Mock validation failed".to_string());
        }
        Ok(())
    }
}

#[tokio::test]
async fn test_custom_verifier_success() -> Result<(), Box<dyn std::error::Error>> {
    let pair = TestSessionPair::create_with_verifier(
        None,
        Some(Box::new(MockVerifier { fail: false, expect_inner_fail: Some(false) })),
    );
    let mut server = AsyncServer::spawn(pair.server_ctx);

    let mut client = do_handshake(&mut server, &pair.client_ctx).await;

    let msg = b"success test";
    let encrypted = client.encrypt(msg)?;
    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    Ok(())
}

#[tokio::test]
async fn test_custom_verifier_failure() -> Result<(), Box<dyn std::error::Error>> {
    let pair = TestSessionPair::create_with_verifier(
        None,
        Some(Box::new(MockVerifier { fail: true, expect_inner_fail: Some(false) })),
    );
    let ctx = pair.server_ctx;
    let mut server = AsyncServer::spawn(ctx);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tokio::task::block_in_place(|| {
            tokio::runtime::Handle::current().block_on(async {
                do_handshake(&mut server, &pair.client_ctx).await;
            })
        });
    }));

    // The handshake should panic because do_handshake uses `.expect("client
    // handshake failed")`. We expect it to fail if our mock verifier works.
    assert!(result.is_err(), "Handshake should have failed due to custom verifier");

    Ok(())
}

#[tokio::test]
async fn test_custom_verifier_invalid_cert() -> Result<(), Box<dyn std::error::Error>> {
    let untrusted_cert = load_test_cert("oak_session/tls/testing/test_untrusted.pem");
    let server_cert = load_test_cert("oak_session/tls/testing/test_server.pem");
    let server_key = load_test_key("oak_session/tls/testing/test_server.key");

    let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: utils::create_static_cert_identity_provider(
            server_key.clone_key(),
            server_cert.clone(),
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    })?;

    // Client trusts untrusted_cert (so server_cert is invalid to it)
    let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(
            untrusted_cert,
        )),
        tls_identity_provider: None,
        custom_cert_verifier: Some(Box::new(MockVerifier {
            fail: true,
            expect_inner_fail: Some(true),
        })),
        expected_server_name: None,
    })?;

    let mut server = AsyncServer::spawn(server_ctx);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tokio::task::block_in_place(|| {
            tokio::runtime::Handle::current().block_on(async {
                do_handshake(&mut server, &client_ctx).await;
            })
        });
    }));

    // Should fail because standard validation rejects the certificate.
    assert!(result.is_err(), "Handshake should have failed due to standard validation");

    Ok(())
}

#[tokio::test]
async fn test_custom_verifier_invalid_self_signed_succeeds_with_custom_ok()
-> Result<(), Box<dyn std::error::Error>> {
    let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
    let untrusted_cert = load_test_cert("oak_session/tls/testing/test_untrusted.pem");
    let untrusted_key = load_test_key("oak_session/tls/testing/test_untrusted.key");

    let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: utils::create_static_cert_identity_provider(
            untrusted_key.clone_key(),
            untrusted_cert.clone(),
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    })?;

    // Client trusts CA, so server's untrusted self-signed is rejected by standard
    // PKI. But custom verifier returns OK.
    let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(ca_cert)),
        tls_identity_provider: None,
        custom_cert_verifier: Some(Box::new(MockVerifier {
            fail: false,
            expect_inner_fail: Some(true),
        })),
        expected_server_name: None,
    })?;

    let mut server = AsyncServer::spawn(server_ctx);

    let mut client = do_handshake(&mut server, &client_ctx).await;

    let msg = b"success test";
    let encrypted = client.encrypt(msg)?;
    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    Ok(())
}

#[tokio::test]
async fn test_custom_verifier_invalid_self_signed_fails_with_custom_error()
-> Result<(), Box<dyn std::error::Error>> {
    let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
    let untrusted_cert = load_test_cert("oak_session/tls/testing/test_untrusted.pem");
    let untrusted_key = load_test_key("oak_session/tls/testing/test_untrusted.key");

    let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: utils::create_static_cert_identity_provider(
            untrusted_key.clone_key(),
            untrusted_cert.clone(),
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    })?;

    // Client trusts CA, so server's untrusted self-signed is rejected.
    // Custom verifier also fails.
    let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(ca_cert)),
        tls_identity_provider: None,
        custom_cert_verifier: Some(Box::new(MockVerifier {
            fail: true,
            expect_inner_fail: Some(true),
        })),
        expected_server_name: None,
    })?;

    let mut server = AsyncServer::spawn(server_ctx);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tokio::task::block_in_place(|| {
            tokio::runtime::Handle::current().block_on(async {
                do_handshake(&mut server, &client_ctx).await;
            })
        });
    }));

    assert!(result.is_err(), "Handshake should have failed due to custom verifier");

    Ok(())
}

#[tokio::test]
async fn test_custom_server_name_match() -> Result<(), Box<dyn std::error::Error>> {
    let custom_name = "my-service.example.com";

    // Server generates a self-signed cert with the custom SAN.
    let server_provider = utils::create_self_signed_for(custom_name)?;
    let server_identity = server_provider.get_identity()?;

    let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: utils::create_static_cert_identity_provider(
            server_identity.key_der.clone_key(),
            server_identity.cert_der.clone(),
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    })?;

    // Client uses a custom verifier to accept the self-signed cert, plus the
    // matching expected_server_name for SAN verification.
    let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: None,
        tls_identity_provider: None,
        custom_cert_verifier: Some(Box::new(MockVerifier { fail: false, expect_inner_fail: None })),
        expected_server_name: Some(custom_name.to_string()),
    })?;

    let mut server = AsyncServer::spawn(server_ctx);
    let mut client = do_handshake(&mut server, &client_ctx).await;

    let msg = b"custom SAN test";
    let encrypted = client.encrypt(msg)?;
    let decrypted = server.decrypt(encrypted).await.unwrap();
    assert_eq!(decrypted, msg);

    Ok(())
}

#[tokio::test]
async fn test_custom_server_name_mismatch_fails() -> Result<(), Box<dyn std::error::Error>> {
    // Server cert has SAN "oak-session-tls" (default).
    let server_provider = utils::create_self_signed()?;
    let server_identity = server_provider.get_identity()?;

    let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: utils::create_static_cert_identity_provider(
            server_identity.key_der.clone_key(),
            server_identity.cert_der.clone(),
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    })?;

    // Client expects a different server name → SAN mismatch.
    let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: None,
        tls_identity_provider: None,
        // Even if custom verifier returns ok, the SAN mismatch in the inner
        // verifier should surface.
        custom_cert_verifier: Some(Box::new(MockVerifier { fail: true, expect_inner_fail: None })),
        expected_server_name: Some("wrong-name.example.com".to_string()),
    })?;

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut server = AsyncServer::spawn(server_ctx);
        tokio::task::block_in_place(|| {
            tokio::runtime::Handle::current().block_on(async {
                do_handshake(&mut server, &client_ctx).await;
            })
        });
    }));

    assert!(result.is_err(), "Handshake should have failed due to SAN mismatch");

    Ok(())
}

#[test]
fn test_create_self_signed_for_custom_name() {
    let custom_name = "my-custom-service.example.com";
    let provider =
        utils::create_self_signed_for(custom_name).expect("create_self_signed_for failed");
    let identity = provider.get_identity().expect("get_identity failed");
    assert!(!identity.cert_der.is_empty());

    // The custom name should appear in the DER-encoded certificate.
    let cert_bytes = identity.cert_der.as_ref();
    let name_bytes = custom_name.as_bytes();
    assert!(
        cert_bytes.windows(name_bytes.len()).any(|w| w == name_bytes),
        "custom server name not found in certificate SAN"
    );
}

struct TestSessionPair {
    pub server_ctx: OakSessionTlsServerContext,
    pub client_ctx: OakSessionTlsClientContext,
}

impl TestSessionPair {
    fn create(client_identity: Option<TlsIdentity>) -> Self {
        Self::create_with_verifier(client_identity, None)
    }

    fn create_with_verifier(
        client_identity: Option<TlsIdentity>,
        custom_cert_verifier: Option<Box<dyn CustomCertVerifier>>,
    ) -> Self {
        let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
        let server_cert = load_test_cert("oak_session/tls/testing/test_server.pem");
        let server_key = load_test_key("oak_session/tls/testing/test_server.key");

        let server_ctx = OakSessionTlsServerContext::create(ServerContextConfig {
            tls_identity_provider: utils::create_static_cert_identity_provider(
                server_key.clone_key(),
                server_cert.clone(),
            ),
            client_trust_anchor_provider: client_identity
                .as_ref()
                .map(|_| utils::create_static_trust_anchor_provider(ca_cert.clone())),
            custom_cert_verifier: None,
        })
        .expect("failed to create server context");

        let client_ctx = OakSessionTlsClientContext::create(ClientContextConfig {
            server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(ca_cert)),
            tls_identity_provider: client_identity
                .map(|id| utils::create_static_cert_identity_provider(id.key_der, id.cert_der)),
            custom_cert_verifier,
            expected_server_name: None,
        })
        .expect("failed to create client context");

        Self { server_ctx, client_ctx }
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
    fn spawn(ctx: OakSessionTlsServerContext) -> Self {
        let (to_server_tls_tx, mut to_server_tls_rx) =
            tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();
        let (from_server_tls_tx, from_server_tls_rx) =
            tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();
        let (from_server_plaintext_tx, from_server_plaintext_rx) =
            tokio::sync::mpsc::unbounded_channel::<Result<Vec<u8>, String>>();
        let (to_server_enc_tx, mut to_server_enc_rx) =
            tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();

        tokio::spawn(async move {
            let (mut server, initial_data) = {
                let rx = Arc::new(Mutex::new(&mut to_server_tls_rx));
                ctx.new_initialized_session(
                    |frame| {
                        let tx = from_server_tls_tx.clone();
                        async move {
                            tx.send(frame)
                                .map_err(|_| std::io::Error::other("send failed"))
                        }
                    },
                    {
                        let rx = rx.clone();
                        move || {
                            let rx = rx.clone();
                            async move { Ok(rx.lock().await.recv().await) }
                        }
                    },
                )
                .await
                .expect("server handshake failed")
            };

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

async fn do_handshake(
    server: &mut AsyncServer,
    client_ctx: &OakSessionTlsClientContext,
) -> OakSessionTls {
    let rx = Arc::new(Mutex::new(&mut server.from_server_tls_rx));
    let (session, initial_data) = client_ctx
        .new_initialized_session(
            |frame| {
                let tx = server.to_server_tls_tx.clone();
                async move { tx.send(frame).map_err(|_| std::io::Error::other("send failed")) }
            },
            {
                let rx = rx.clone();
                move || {
                    let rx = rx.clone();
                    async move { Ok(rx.lock().await.recv().await) }
                }
            },
        )
        .await
        .expect("client handshake failed");

    if !initial_data.is_empty() {
        println!("Client: Received {} bytes of initial data during handshake", initial_data.len());
    }
    session
}

#[test]
fn test_create_self_signed_no_extensions() {
    let provider = utils::create_self_signed().expect("create_self_signed failed");
    let identity = provider.get_identity().expect("get_identity failed");
    assert!(!identity.cert_der.is_empty());
}

#[test]
fn test_create_self_signed_with_extensions() {
    let ext = rcgen::CustomExtension::from_oid_content(
        &[1, 2, 3, 4, 5, 6, 7, 8, 9],
        b"test-attestation-data".to_vec(),
    );
    let provider = utils::create_self_signed_with_extensions(vec![ext])
        .expect("create_self_signed_with_extensions failed");
    let identity = provider.get_identity().expect("get_identity failed");
    assert!(!identity.cert_der.is_empty());

    // The extension OID 1.2.3.4.5.6.7.8.9 should appear in the DER-encoded
    // cert as its BER encoding: 2a.03.04.05.06.07.08.09
    // (first two arcs 1.2 merge into 0x2a, rest are single-byte).
    let cert_bytes = identity.cert_der.as_ref();
    let oid_bytes: &[u8] = &[0x2a, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09];
    assert!(
        cert_bytes.windows(oid_bytes.len()).any(|w| w == oid_bytes),
        "extension OID not found in certificate DER"
    );
}

#[test]
fn test_create_self_signed_with_multiple_extensions() {
    let ext1 = rcgen::CustomExtension::from_oid_content(&[1, 2, 3, 4, 5, 100], b"first".to_vec());
    let ext2 =
        rcgen::CustomExtension::from_oid_content(&[1, 2, 3, 4, 5, 200, 1], b"second".to_vec());
    let provider = utils::create_self_signed_with_extensions(vec![ext1, ext2])
        .expect("create_self_signed_with_extensions failed");
    let identity = provider.get_identity().expect("get_identity failed");
    assert!(!identity.cert_der.is_empty());
}
