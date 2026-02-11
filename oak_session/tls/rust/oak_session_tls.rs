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
    io::{Read, Write},
    sync::Arc,
};

use rustls::{
    ClientConfig, ClientConnection, Connection, RootCertStore, ServerConfig, ServerConnection,
    client::WebPkiServerVerifier, server::WebPkiClientVerifier,
};
use rustls_pki_types::{CertificateDer, InvalidDnsNameError, PrivateKeyDer, ServerName};
use thiserror::Error;

/// The server name used for SNI and certificate verification during the TLS
/// handshake.
///
/// This specific string is chosen as a service identifier for Oak Session TLS.
/// The choice of string is arbitrary, but it must be consistent between the
/// client and the server's certificate. The client uses this name to populate
/// the Server Name Indication (SNI) extension and to verify that the server's
/// certificate is valid for this identity.
///
/// Note: The server side currently does not validate the SNI, as it is
/// configured with a single certificate that is used for all incoming
/// connections.
const OAK_SESSION_TLS_SERVER_NAME: &str = "oak-session-tls";

/// The Application-Layer Protocol Negotiation (ALPN) protocol ID used for Oak
/// Session TLS.
///
/// This identifier ensures that both the client and server agree to use the
/// same protocol over the TLS connection.
const OAK_SESSION_TLS_ALPN_PROTOCOL: &[u8] = b"oak-session-tls";

/// Errors that can occur during the creation of an Oak Session TLS Context.
#[derive(Error, Debug)]
pub enum ContextError {
    #[error("failed to create config: {0}")]
    Config(#[from] rustls::Error),
    #[error("root cert store error: {0}")]
    VerifierBuilder(#[from] rustls::client::VerifierBuilderError),
}

/// Errors that can occur during session initialization and handshake.
#[derive(Error, Debug)]
pub enum InitializationError {
    #[error("invalid server name: {0}")]
    InvalidServerName(#[from] InvalidDnsNameError),
    #[error("handshake not finished")]
    HandshakeNotFinished,
    #[error("TLS error: {0}")]
    Tls(#[from] rustls::Error),
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Unexpected EOF trying to write data into TLS buffer")]
    UnexpectedEof,
}

/// Errors that can occur during the handshake.
#[derive(Error, Debug)]
pub enum HandshakeError<E: std::fmt::Display + std::fmt::Debug> {
    #[error("initialization error: {0}")]
    Initialization(#[from] InitializationError),
    #[error("I/O error: {0}")]
    Io(E),
}

/// Errors that can occur in an open Oak Session TLS.
#[derive(Error, Debug)]
pub enum SessionError {
    #[error("TLS error: {0}")]
    Tls(#[from] rustls::Error),
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Could not write any more data into the TLS buffer")]
    TLSBufferFull,
    #[error("Unexpected EOF trying to write data into TLS buffer")]
    UnexpectedEof,
}

/// The public/private key pair that this node will use.
pub struct TlsIdentity {
    /// The private key that this node will use during handshake.
    pub key_der: PrivateKeyDer<'static>,
    /// The certificate containing the public key corresponding to the private
    /// key.
    pub cert_der: CertificateDer<'static>,
}

/// Parameters to configure OakSessionTlsServerContext for server behavior.
pub struct ServerContextConfig {
    /// The key and certificate to use for this server.
    pub tls_identity: TlsIdentity,
    /// Optional trust anchor for the client.
    /// If set, client verification will be required.
    pub client_trust_anchor_der: Option<CertificateDer<'static>>,
}

/// Parameters to configure OakSessionTlsClientContext for client behavior.
pub struct ClientContextConfig {
    /// The trust anchor that can verify the server.
    pub server_trust_anchor_der: Option<CertificateDer<'static>>,
    /// If provided, the client will support (but not require) mTLS mode.
    pub tls_identity: Option<TlsIdentity>,
}

/// Manages a TLS configuration that will be used to create Oak TLS client
/// sessions.
pub struct OakSessionTlsClientContext {
    config: Arc<ClientConfig>,
}

impl OakSessionTlsClientContext {
    /// Creates a new OakSessionTlsClientContext.
    pub fn create(config: ClientContextConfig) -> Result<Self, ContextError> {
        ensure_crypto_provider();

        let mut root_store = RootCertStore::empty();
        if let Some(trust_anchor) = config.server_trust_anchor_der {
            root_store.add(trust_anchor)?;
        }
        let verifier = WebPkiServerVerifier::builder(Arc::new(root_store)).build()?;
        let builder = ClientConfig::builder().with_webpki_verifier(verifier);

        let mut client_config = if let Some(identity) = config.tls_identity {
            let certs = vec![identity.cert_der];
            let key = identity.key_der;
            builder.with_client_auth_cert(certs, key)?
        } else {
            builder.with_no_client_auth()
        };

        client_config.alpn_protocols = vec![OAK_SESSION_TLS_ALPN_PROTOCOL.to_vec()];

        Ok(Self { config: Arc::new(client_config) })
    }

    /// Create a new OakSessionTlsInitializer for a new client session using
    /// this context's current configuration.
    pub fn new_session(&self) -> Result<OakSessionTlsInitializer, InitializationError> {
        // The server side currently does not validate the SNI, but rustls requires
        // a server name to be provided for the client to initiate the handshake
        // and perform certificate verification.
        Ok(OakSessionTlsInitializer {
            who: "client".to_string(),
            connection: Connection::Client(ClientConnection::new(
                self.config.clone(),
                // The server side currently does not validate the SNI, but rustls requires
                // a server name to be provided for the client to initiate the handshake
                // and perform certificate verification.
                ServerName::try_from(OAK_SESSION_TLS_SERVER_NAME)?.to_owned(),
            )?),
        })
    }
}

/// Manages a TLS configuration that will be used to create Oak TLS server
/// sessions.
pub struct OakSessionTlsServerContext {
    config: Arc<ServerConfig>,
}

impl OakSessionTlsServerContext {
    /// Creates a new OakSessionTlsServerContext.
    pub fn create(config: ServerContextConfig) -> Result<Self, ContextError> {
        ensure_crypto_provider();

        let certs = vec![config.tls_identity.cert_der];
        let key = config.tls_identity.key_der;

        let builder = if let Some(trust_anchor) = config.client_trust_anchor_der {
            let mut root_store = RootCertStore::empty();
            root_store.add(trust_anchor)?;
            let verifier = WebPkiClientVerifier::builder(Arc::new(root_store)).build()?;
            ServerConfig::builder().with_client_cert_verifier(verifier)
        } else {
            ServerConfig::builder().with_no_client_auth()
        };

        let mut server_config = builder.with_single_cert(certs, key)?;

        server_config.alpn_protocols = vec![OAK_SESSION_TLS_ALPN_PROTOCOL.to_vec()];

        Ok(Self { config: Arc::new(server_config) })
    }

    /// Create a new OakSessionTlsInitializer for a new server session using
    /// this context's current configuration.
    pub fn new_session(&self) -> Result<OakSessionTlsInitializer, InitializationError> {
        Ok(OakSessionTlsInitializer {
            who: "server".to_string(),
            connection: Connection::Server(ServerConnection::new(self.config.clone())?),
        })
    }
}

/// Manages the initialization state and handshake of an Oak TLS Session.
///
/// In this context, a "TLS frame" is an arbitrary slice of the TLS stream.
///
/// While handshaking, provided incoming frames to `put_tls_frame` and retrieve
/// outgoing frames via `get_tls_frame`. Check `is_ready` to determine when the
/// handshake is complete.
///
/// Use either [`OakSessionTlsClientContext`] or [`OakSessionTlsServerContext`]
/// to create an initializer.
pub struct OakSessionTlsInitializer {
    pub connection: Connection,
    pub who: String,
}

impl OakSessionTlsInitializer {
    /// Provide an incoming TLS frame to the initializer.
    /// Returns any application data received during the handshake.
    pub fn put_tls_frame(&mut self, mut frame: &[u8]) -> Result<Vec<u8>, InitializationError> {
        let n = self.connection.read_tls(&mut frame)?;
        if n == 0 {
            return Err(InitializationError::UnexpectedEof);
        }
        self.connection.process_new_packets()?;
        let mut result = Vec::new();
        let _ = self.connection.reader().read_to_end(&mut result);
        Ok(result)
    }

    /// Retrieve the next outgoing TLS frame.
    pub fn get_tls_frame(&mut self) -> Result<Vec<u8>, InitializationError> {
        let mut buffer = Vec::new();
        let _ = self.connection.write_tls(&mut buffer)?;
        Ok(buffer)
    }

    /// Returns true if the handshake is complete.
    pub fn is_ready(&self) -> bool {
        !self.connection.is_handshaking() && !self.connection.wants_write()
    }

    /// Returns the open Oak TLS session, any initial application data received
    /// during the handshake, and any pending TLS data to be sent for completing
    /// the handshake.
    ///
    /// Consumes the initializer. Returns an error if the handshake is not yet
    /// complete.
    pub fn get_open_session(self) -> Result<(OakSessionTls, Vec<u8>), InitializationError> {
        if !self.is_ready() {
            return Err(InitializationError::HandshakeNotFinished);
        }
        let mut session = OakSessionTls { connection: self.connection };
        let mut initial_data = Vec::new();
        session.drain_plaintext(&mut initial_data)?;
        Ok((session, initial_data))
    }

    /// Drives the handshake to completion using the provided sender and
    /// receiver closures.
    pub async fn handshake<S, FutS, R, FutR, E>(
        mut self,
        mut sender: S,
        mut receiver: R,
    ) -> Result<(OakSessionTls, Vec<u8>), HandshakeError<E>>
    where
        S: FnMut(Vec<u8>) -> FutS,
        FutS: std::future::Future<Output = Result<(), E>>,
        R: FnMut() -> FutR,
        FutR: std::future::Future<Output = Result<Option<Vec<u8>>, E>>,
        E: std::fmt::Display + std::fmt::Debug,
    {
        while !self.is_ready() {
            let frame = self.get_tls_frame()?;
            if !frame.is_empty() {
                sender(frame).await.map_err(HandshakeError::Io)?;
            }

            if !self.is_ready() {
                if let Some(frame) = receiver().await.map_err(HandshakeError::Io)? {
                    let _ = self.put_tls_frame(&frame)?;
                } else {
                    break;
                }
            }
        }

        Ok(self.get_open_session()?)
    }
}

/// Represents an open Oak Session (TLS) used for encryption and decryption.
///
/// Use [`OakSessionTlsInitializer`] to create an instance.
pub struct OakSessionTls {
    connection: Connection,
}

impl OakSessionTls {
    /// Encrypts the plaintext and returns the corresponding TLS frames.
    pub fn encrypt(&mut self, mut plaintext: &[u8]) -> Result<Vec<u8>, SessionError> {
        let mut result = Vec::new();
        while !plaintext.is_empty() {
            let written = self.connection.writer().write(plaintext)?;
            plaintext = &plaintext[written..];
            let _ = self.connection.write_tls(&mut result)?;
            if written == 0 {
                // If we didn't write anything, we should check if there's anything else to
                // write.
                let n = self.connection.write_tls(&mut result)?;
                if n == 0 {
                    return Err(SessionError::TLSBufferFull);
                }
            }
        }
        // Always try to drain any remaining TLS data.
        let _ = self.connection.write_tls(&mut result)?;
        Ok(result)
    }

    /// Decrypts the provided TLS frames and returns any application plaintext
    /// and any outgoing TLS frames produced (e.g. post-handshake messages).
    ///
    /// If the frames contain partial TLS records, the engine will buffer the
    /// data until sufficient frames are provided in subsequent calls.
    ///
    /// This method returns `DecryptionBufferFull` if the provided data exceeds
    /// the internal buffer's current capacity.
    pub fn decrypt(&mut self, mut frames: &[u8]) -> Result<Vec<u8>, SessionError> {
        let mut plaintext = Vec::new();
        while !frames.is_empty() {
            let n = self.connection.read_tls(&mut frames)?;
            if n == 0 {
                return Err(SessionError::UnexpectedEof);
            }
            self.connection.process_new_packets()?;
            self.drain_plaintext(&mut plaintext)?;
        }
        Ok(plaintext)
    }

    fn drain_plaintext(&mut self, result: &mut Vec<u8>) -> Result<(), std::io::Error> {
        match self.connection.reader().read_to_end(result) {
            Ok(_) => Ok(()),
            // If we get [`std::io::ErrorKind::WouldBlock`]`, it means there is no more plaintext to
            // read at the moment, but that's OK here, we just want to return any
            // data that's already availble.
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => Ok(()),
            Err(e) => Err(e),
        }
    }
}

fn ensure_crypto_provider() {
    let _ = rustls::crypto::ring::default_provider().install_default();
}

// --- Config Helper Utilities ---

pub mod utils {
    use std::io::BufRead;

    use rustls_pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};

    pub fn load_cert_der<R: BufRead>(mut reader: R) -> CertificateDer<'static> {
        rustls_pemfile::certs(&mut reader).next().unwrap().unwrap()
    }

    pub fn load_key_der<R: BufRead>(mut reader: R) -> PrivateKeyDer<'static> {
        let key_der = rustls_pemfile::private_key(&mut reader).unwrap().unwrap();
        parse_private_key(key_der.secret_der().to_vec())
    }

    fn parse_private_key(der: Vec<u8>) -> PrivateKeyDer<'static> {
        // We currently assume PKCS#8 DER format for private keys.
        PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(der))
    }
}
