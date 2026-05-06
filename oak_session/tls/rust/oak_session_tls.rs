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
    ClientConfig, ClientConnection, Connection, DigitallySignedStruct, RootCertStore, ServerConfig,
    ServerConnection, SignatureScheme,
    client::{
        WebPkiServerVerifier,
        danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier},
    },
    server::{
        WebPkiClientVerifier,
        danger::{ClientCertVerified, ClientCertVerifier},
    },
};
use rustls_pki_types::{CertificateDer, InvalidDnsNameError, PrivateKeyDer, ServerName, UnixTime};
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
    #[error("failed to generate certificate: {0}")]
    CertGen(String),
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
    #[error("unexpected EOF trying to write data into TLS buffer")]
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
    #[error("could not write any more data into the TLS buffer")]
    TLSBufferFull,
    #[error("unexpected EOF trying to write data into TLS buffer")]
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

/// Provider trait that returns a TlsIdentity.
/// Called each time a new session is created on the context.
pub trait TlsIdentityProvider: Send + Sync {
    fn get_identity(&self) -> Result<TlsIdentity, ContextError>;
}

impl<F> TlsIdentityProvider for F
where
    F: Fn() -> Result<TlsIdentity, ContextError> + Send + Sync,
{
    fn get_identity(&self) -> Result<TlsIdentity, ContextError> {
        self()
    }
}

/// Custom certificate verification logic that will be run in addition to
/// standard verification.
///
/// The `verify` method is called with the result of standard verification,
/// allowing it to make decisions based on whether standard verification
/// succeeded or failed, and with what specific error.
pub trait CustomCertVerifier: Send + Sync + std::fmt::Debug {
    /// Verify the certificate chain.
    ///
    /// `verify_result` contains the result of standard verification.
    /// Returns Ok(()) if the certificate should be accepted (overriding any
    /// standard verification failure), or Err(String) to reject it.
    fn verify(
        &self,
        end_entity: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        verify_result: Result<(), &rustls::Error>,
    ) -> Result<(), String>;
}

/// Parameters to configure OakSessionTlsServerContext for server behavior.
pub struct ServerContextConfig {
    /// Provider that returns the key and certificate for this server.
    /// Called each time a new session is created.
    pub tls_identity_provider: Box<dyn TlsIdentityProvider>,
    /// Optional trust anchor for the client.
    /// If set, client verification will be required.
    pub client_trust_anchor_der: Option<CertificateDer<'static>>,
    /// Optional custom certificate verifier. If provided, it will be called
    /// with the result of standard verification, allowing it to override
    /// failures or add additional checks.
    pub custom_cert_verifier: Option<Box<dyn CustomCertVerifier>>,
}

/// Parameters to configure OakSessionTlsClientContext for client behavior.
pub struct ClientContextConfig {
    /// The trust anchor that can verify the server.
    pub server_trust_anchor_der: Option<CertificateDer<'static>>,
    /// If provided, called each time a new session is created to get the
    /// client's TLS identity. Enables mTLS mode.
    pub tls_identity_provider: Option<Box<dyn TlsIdentityProvider>>,
    /// Optional custom certificate verifier. If provided, it will be called
    /// with the result of standard verification, allowing it to override
    /// failures or add additional checks.
    pub custom_cert_verifier: Option<Box<dyn CustomCertVerifier>>,
    /// The expected server name for SNI and certificate SAN verification.
    ///
    /// This value is used for two purposes:
    /// 1. It populates the Server Name Indication (SNI) extension in the TLS
    ///    ClientHello.
    /// 2. It is matched against the server certificate's Subject Alternative
    ///    Name (SAN) during WebPKI verification.
    ///
    /// If not set, defaults to `"oak-session-tls"`.
    pub expected_server_name: Option<String>,
}

#[derive(Debug)]
struct DelegatingServerCertVerifier {
    inner: Arc<dyn ServerCertVerifier>,
    custom: Box<dyn CustomCertVerifier>,
}

impl ServerCertVerifier for DelegatingServerCertVerifier {
    fn verify_server_cert(
        &self,
        end_entity: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        server_name: &ServerName<'_>,
        ocsp_response: &[u8],
        now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        let verified_res = self.inner.verify_server_cert(
            end_entity,
            intermediates,
            server_name,
            ocsp_response,
            now,
        );

        let verify_result = verified_res.as_ref().map(|_| ());

        let custom_result = self.custom.verify(end_entity, intermediates, verify_result);

        if custom_result.is_ok() {
            return verified_res.or_else(|_| Ok(ServerCertVerified::assertion()));
        }

        verified_res?;

        Err(rustls::Error::General(format!(
            "Custom verification failed: {}",
            custom_result.unwrap_err()
        )))
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        self.inner.verify_tls12_signature(message, cert, dss)
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        self.inner.verify_tls13_signature(message, cert, dss)
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.inner.supported_verify_schemes()
    }
}

#[derive(Debug)]
struct DelegatingClientCertVerifier {
    inner: Arc<dyn ClientCertVerifier>,
    custom: Box<dyn CustomCertVerifier>,
}

impl ClientCertVerifier for DelegatingClientCertVerifier {
    fn offer_client_auth(&self) -> bool {
        self.inner.offer_client_auth()
    }

    fn client_auth_mandatory(&self) -> bool {
        self.inner.client_auth_mandatory()
    }

    fn root_hint_subjects(&self) -> &[rustls::DistinguishedName] {
        self.inner.root_hint_subjects()
    }

    fn verify_client_cert(
        &self,
        end_entity: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        now: UnixTime,
    ) -> Result<ClientCertVerified, rustls::Error> {
        let verified_res = self.inner.verify_client_cert(end_entity, intermediates, now);

        let verify_result = verified_res.as_ref().map(|_| ());

        let custom_result = self.custom.verify(end_entity, intermediates, verify_result);

        if custom_result.is_ok() {
            return verified_res.or_else(|_| Ok(ClientCertVerified::assertion()));
        }

        verified_res?;

        Err(rustls::Error::General(format!(
            "Custom verification failed: {}",
            custom_result.unwrap_err()
        )))
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        self.inner.verify_tls12_signature(message, cert, dss)
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        self.inner.verify_tls13_signature(message, cert, dss)
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.inner.supported_verify_schemes()
    }
}

/// A standalone server certificate verifier that delegates entirely to a
/// [`CustomCertVerifier`], without performing any standard WebPKI validation.
///
/// Used when no trust anchors are configured but custom verification (such as
/// attestation-based checks) is desired.
#[derive(Debug)]
struct CustomOnlyServerCertVerifier {
    custom: Box<dyn CustomCertVerifier>,
}

impl ServerCertVerifier for CustomOnlyServerCertVerifier {
    fn verify_server_cert(
        &self,
        end_entity: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        _server_name: &ServerName<'_>,
        _ocsp_response: &[u8],
        _now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        // No standard verification was performed, so pass Err to the custom
        // verifier indicating that standard verification is not available.
        let verify_result = Err(&rustls::Error::UnsupportedNameType);
        self.custom
            .verify(end_entity, intermediates, verify_result)
            .map(|_| ServerCertVerified::assertion())
            .map_err(|e| rustls::Error::General(format!("custom verification failed: {e}")))
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        rustls::crypto::ring::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }
}

/// A standalone client certificate verifier that delegates entirely to a
/// [`CustomCertVerifier`], without performing any standard WebPKI validation.
///
/// Used when no trust anchors are configured but custom verification (such as
/// attestation-based checks) is desired.
#[derive(Debug)]
struct CustomOnlyClientCertVerifier {
    custom: Box<dyn CustomCertVerifier>,
}

impl ClientCertVerifier for CustomOnlyClientCertVerifier {
    fn offer_client_auth(&self) -> bool {
        true
    }

    fn client_auth_mandatory(&self) -> bool {
        true
    }

    fn root_hint_subjects(&self) -> &[rustls::DistinguishedName] {
        &[]
    }

    fn verify_client_cert(
        &self,
        end_entity: &CertificateDer<'_>,
        intermediates: &[CertificateDer<'_>],
        _now: UnixTime,
    ) -> Result<ClientCertVerified, rustls::Error> {
        let verify_result = Err(&rustls::Error::UnsupportedNameType);
        self.custom
            .verify(end_entity, intermediates, verify_result)
            .map(|_| ClientCertVerified::assertion())
            .map_err(|e| rustls::Error::General(format!("custom verification failed: {e}")))
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        rustls::crypto::ring::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }
}

/// Manages a TLS configuration that will be used to create Oak TLS client
/// sessions.
pub struct OakSessionTlsClientContext {
    verifier: Arc<dyn rustls::client::danger::ServerCertVerifier>,
    tls_identity_provider: Option<Box<dyn TlsIdentityProvider>>,
    server_name: String,
}

impl OakSessionTlsClientContext {
    /// Creates a new OakSessionTlsClientContext.
    pub fn create(config: ClientContextConfig) -> Result<Self, ContextError> {
        ensure_crypto_provider();

        let verifier: Arc<dyn rustls::client::danger::ServerCertVerifier> =
            match (config.server_trust_anchor_der, config.custom_cert_verifier) {
                (Some(trust_anchor), custom) => {
                    let mut root_store = RootCertStore::empty();
                    root_store.add(trust_anchor)?;
                    let inner = WebPkiServerVerifier::builder(Arc::new(root_store)).build()?;
                    if let Some(custom) = custom {
                        Arc::new(DelegatingServerCertVerifier { inner, custom })
                    } else {
                        inner
                    }
                }
                (None, Some(custom)) => Arc::new(CustomOnlyServerCertVerifier { custom }),
                (None, None) => {
                    let root_store = RootCertStore::empty();
                    WebPkiServerVerifier::builder(Arc::new(root_store)).build()?
                }
            };

        let server_name =
            config.expected_server_name.unwrap_or_else(|| OAK_SESSION_TLS_SERVER_NAME.to_string());

        Ok(Self { verifier, tls_identity_provider: config.tls_identity_provider, server_name })
    }

    /// Create a new OakSessionTlsInitializer for a new client session using
    /// this context's current configuration.
    ///
    /// Use this only if you need to drive the handshake yourself (e.g., for
    /// custom transport framing). For most use cases, prefer
    /// [`new_initialized_session`](Self::new_initialized_session) instead.
    pub fn new_session(&self) -> Result<OakSessionTlsInitializer, InitializationError> {
        let builder = ClientConfig::builder()
            .dangerous()
            .with_custom_certificate_verifier(self.verifier.clone());

        let mut client_config = if let Some(provider) = &self.tls_identity_provider {
            let identity = provider
                .get_identity()
                .map_err(|e| InitializationError::Tls(rustls::Error::General(e.to_string())))?;
            let certs = vec![identity.cert_der];
            let key = identity.key_der;
            builder.with_client_auth_cert(certs, key).map_err(InitializationError::Tls)?
        } else {
            builder.with_no_client_auth()
        };

        client_config.alpn_protocols = vec![OAK_SESSION_TLS_ALPN_PROTOCOL.to_vec()];

        Ok(OakSessionTlsInitializer {
            who: "client".to_string(),
            connection: Connection::Client(ClientConnection::new(
                Arc::new(client_config),
                ServerName::try_from(self.server_name.as_str())?.to_owned(),
            )?),
        })
    }

    /// Create a new session and perform the TLS handshake using the provided
    /// send/receive callbacks. Returns an initialized session ready for use.
    ///
    /// This is the recommended API for most use cases.
    ///
    /// # Example
    /// ```ignore
    /// let (session, initial_data) = context.new_initialized_session(
    ///     |frame| async { socket.send(frame).await },
    ///     || async { socket.receive().await },
    /// ).await?;
    /// ```
    pub async fn new_initialized_session<S, FutS, R, FutR, E>(
        &self,
        sender: S,
        receiver: R,
    ) -> Result<(OakSessionTls, Vec<u8>), HandshakeError<E>>
    where
        S: FnMut(Vec<u8>) -> FutS,
        FutS: std::future::Future<Output = Result<(), E>>,
        R: FnMut() -> FutR,
        FutR: std::future::Future<Output = Result<Option<Vec<u8>>, E>>,
        E: std::fmt::Display + std::fmt::Debug,
    {
        let initializer = self.new_session()?;
        initializer.handshake(sender, receiver).await
    }
}

/// Manages a TLS configuration that will be used to create Oak TLS server
/// sessions.
pub struct OakSessionTlsServerContext {
    tls_identity_provider: Box<dyn TlsIdentityProvider>,
    client_verifier: Option<Arc<dyn rustls::server::danger::ClientCertVerifier>>,
}

impl OakSessionTlsServerContext {
    /// Creates a new OakSessionTlsServerContext.
    pub fn create(config: ServerContextConfig) -> Result<Self, ContextError> {
        ensure_crypto_provider();

        let client_verifier: Option<Arc<dyn rustls::server::danger::ClientCertVerifier>> =
            match (config.client_trust_anchor_der, config.custom_cert_verifier) {
                (Some(trust_anchor), custom) => {
                    let mut root_store = RootCertStore::empty();
                    root_store.add(trust_anchor)?;
                    let inner = WebPkiClientVerifier::builder(Arc::new(root_store)).build()?;
                    if let Some(custom) = custom {
                        Some(Arc::new(DelegatingClientCertVerifier { inner, custom }))
                    } else {
                        Some(inner)
                    }
                }
                (None, Some(custom)) => Some(Arc::new(CustomOnlyClientCertVerifier { custom })),
                (None, None) => None,
            };

        Ok(Self { tls_identity_provider: config.tls_identity_provider, client_verifier })
    }

    /// Create a new OakSessionTlsInitializer for a new server session using
    /// this context's current configuration.
    ///
    /// Use this only if you need to drive the handshake yourself (e.g., for
    /// custom transport framing). For most use cases, prefer
    /// [`new_initialized_session`](Self::new_initialized_session) instead.
    pub fn new_session(&self) -> Result<OakSessionTlsInitializer, InitializationError> {
        let builder = if let Some(verifier) = &self.client_verifier {
            ServerConfig::builder().with_client_cert_verifier(verifier.clone())
        } else {
            ServerConfig::builder().with_no_client_auth()
        };

        let identity = self
            .tls_identity_provider
            .get_identity()
            .map_err(|e| InitializationError::Tls(rustls::Error::General(e.to_string())))?;
        let certs = vec![identity.cert_der];
        let key = identity.key_der;

        let mut server_config =
            builder.with_single_cert(certs, key).map_err(InitializationError::Tls)?;

        server_config.alpn_protocols = vec![OAK_SESSION_TLS_ALPN_PROTOCOL.to_vec()];

        Ok(OakSessionTlsInitializer {
            who: "server".to_string(),
            connection: Connection::Server(ServerConnection::new(Arc::new(server_config))?),
        })
    }

    /// Create a new session and perform the TLS handshake using the provided
    /// send/receive callbacks. Returns an initialized session ready for use.
    ///
    /// This is the recommended API for most use cases.
    ///
    /// # Example
    /// ```ignore
    /// let (session, initial_data) = context.new_initialized_session(
    ///     |frame| async { socket.send(frame).await },
    ///     || async { socket.receive().await },
    /// ).await?;
    /// ```
    pub async fn new_initialized_session<S, FutS, R, FutR, E>(
        &self,
        sender: S,
        receiver: R,
    ) -> Result<(OakSessionTls, Vec<u8>), HandshakeError<E>>
    where
        S: FnMut(Vec<u8>) -> FutS,
        FutS: std::future::Future<Output = Result<(), E>>,
        R: FnMut() -> FutR,
        FutR: std::future::Future<Output = Result<Option<Vec<u8>>, E>>,
        E: std::fmt::Display + std::fmt::Debug,
    {
        let initializer = self.new_session()?;
        initializer.handshake(sender, receiver).await
    }
}

/// Manages the initialization state and handshake of an Oak TLS Session.
///
/// For most use cases, prefer
/// [`OakSessionTlsClientContext::new_initialized_session`] or
/// [`OakSessionTlsServerContext::new_initialized_session`] which handle
/// the full handshake automatically. Use this type directly only if you need
/// fine-grained control over the handshake process (e.g., for custom framing).
///
/// In this context, a "TLS frame" is an arbitrary slice of the TLS stream.
///
/// While handshaking, provide incoming frames to `put_tls_frame` and retrieve
/// outgoing frames via `get_tls_frame`. Check `is_ready` to determine when the
/// handshake is complete.
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
    pub(crate) async fn handshake<S, FutS, R, FutR, E>(
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

    use super::{ContextError, OAK_SESSION_TLS_SERVER_NAME, TlsIdentity, TlsIdentityProvider};

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

    /// Creates a TlsIdentityProvider that always returns the provided static
    /// key and certificate.
    pub fn create_static_cert_identity_provider(
        key_der: PrivateKeyDer<'static>,
        cert_der: CertificateDer<'static>,
    ) -> Box<dyn TlsIdentityProvider> {
        // Clone the content to allow the closure to return them multiple times
        let key_der_bytes = key_der.secret_der().to_vec();
        let cert_der_bytes = cert_der.as_ref().to_vec();

        Box::new(move || {
            Ok(TlsIdentity {
                key_der: PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key_der_bytes.clone())),
                cert_der: CertificateDer::from(cert_der_bytes.clone()),
            })
        })
    }

    /// Creates a TlsIdentityProvider that generates an ephemeral self-signed
    /// certificate upon construction.
    ///
    /// The certificate's Subject Alternative Name (SAN) is set to the default
    /// Oak Session TLS server name (`"oak-session-tls"`).
    pub fn create_self_signed() -> Result<Box<dyn TlsIdentityProvider>, ContextError> {
        create_self_signed_with_extensions(Vec::new())
    }

    /// Creates a TlsIdentityProvider that generates an ephemeral self-signed
    /// certificate for the given server name.
    ///
    /// The `server_name` is embedded as the certificate's Subject Alternative
    /// Name (SAN), which must match the client's `expected_server_name` for
    /// WebPKI verification to succeed.
    pub fn create_self_signed_for(
        server_name: &str,
    ) -> Result<Box<dyn TlsIdentityProvider>, ContextError> {
        create_self_signed_with_extensions_for(server_name, Vec::new())
    }

    /// Creates a TlsIdentityProvider that generates an ephemeral self-signed
    /// certificate with the specified X.509v3 extensions.
    ///
    /// The certificate's SAN is set to the default Oak Session TLS server name
    /// (`"oak-session-tls"`).
    ///
    /// Use [`rcgen::CustomExtension::from_oid_content`] to create extensions.
    ///
    /// # Example
    /// ```ignore
    /// let ext = rcgen::CustomExtension::from_oid_content(
    ///     &[1, 2, 3, 4, 5],
    ///     b"attestation-evidence".to_vec(),
    /// );
    /// let provider = create_self_signed_with_extensions(vec![ext])?;
    /// ```
    pub fn create_self_signed_with_extensions(
        extensions: Vec<rcgen::CustomExtension>,
    ) -> Result<Box<dyn TlsIdentityProvider>, ContextError> {
        create_self_signed_with_extensions_for(OAK_SESSION_TLS_SERVER_NAME, extensions)
    }

    /// Creates a TlsIdentityProvider that generates an ephemeral self-signed
    /// certificate for the given server name with the specified X.509v3
    /// extensions.
    ///
    /// The `server_name` is embedded as the certificate's Subject Alternative
    /// Name (SAN), which must match the client's `expected_server_name` for
    /// WebPKI verification to succeed.
    ///
    /// Use [`rcgen::CustomExtension::from_oid_content`] to create extensions.
    pub fn create_self_signed_with_extensions_for(
        server_name: &str,
        extensions: Vec<rcgen::CustomExtension>,
    ) -> Result<Box<dyn TlsIdentityProvider>, ContextError> {
        let subject_alt_names = vec![server_name.to_string()];
        let mut params = rcgen::CertificateParams::new(subject_alt_names)
            .map_err(|e| ContextError::CertGen(e.to_string()))?;

        params.custom_extensions = extensions;

        let key_pair = rcgen::KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256)
            .map_err(|e| ContextError::CertGen(e.to_string()))?;

        let cert =
            params.self_signed(&key_pair).map_err(|e| ContextError::CertGen(e.to_string()))?;

        let key_der_bytes = key_pair.serialize_der();
        let cert_der_bytes = cert.der().to_vec();

        Ok(Box::new(move || {
            Ok(TlsIdentity {
                key_der: PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key_der_bytes.clone())),
                cert_der: CertificateDer::from(cert_der_bytes.clone()),
            })
        }))
    }
}
