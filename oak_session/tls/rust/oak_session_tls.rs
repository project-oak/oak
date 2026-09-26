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

/// Returns `Some(err)` if `verified_res` failed for a reason a
/// [`CustomCertVerifier`] must never be allowed to override: the identity
/// asserted by the certificate not matching the peer being connected to
/// (`NotValidForName`), or the certificate itself being invalid on its face
/// (expired, not yet valid, or a broken cryptographic signature over the
/// chain). `CustomCertVerifier` exists to relax *trust-anchor* decisions
/// (`UnknownIssuer` and similar, where the chain and dates check out but the
/// root is not one standard WebPKI validation recognizes) -- not to launder a
/// certificate that fails verification for one of these structural reasons.
/// Returning `Ok` from a custom verifier must not be able to override any of
/// these, regardless of what the custom verifier itself decides.
fn critical_verification_failure<T>(
    verified_res: &Result<T, rustls::Error>,
) -> Option<rustls::Error> {
    if let Err(rustls::Error::InvalidCertificate(cert_err)) = verified_res {
        if matches!(
            cert_err,
            rustls::CertificateError::NotValidForName
                | rustls::CertificateError::Expired
                | rustls::CertificateError::ExpiredContext { .. }
                | rustls::CertificateError::NotValidYet
                | rustls::CertificateError::NotValidYetContext { .. }
                | rustls::CertificateError::BadSignature
        ) {
            return Some(rustls::Error::InvalidCertificate(cert_err.clone()));
        }
    }
    None
}

/// The [`critical_verification_failure`] check, narrowed for
/// [`CustomOnlyServerCertVerifier`] specifically.
///
/// That verifier's `inner` is always built against a `RootCertStore`
/// containing an arbitrary, unrelated dummy self-signed certificate (see
/// `build_verifier`'s `(None, Some(custom))` arm) -- there is no real trust
/// anchor to check against by design, since the custom verifier is meant to
/// be the entire trust decision. Confirmed empirically: `rustls-webpki`'s
/// path-building finds that dummy certificate as a chain-building candidate
/// and attempts to verify the presented certificate's signature against it,
/// which fails -- reported as `BadSignature` -- for *any* certificate not
/// actually signed by that arbitrary dummy key, including a completely
/// valid, non-expired one. This failure mode also masks a genuinely expired
/// certificate behind the same `BadSignature` result rather than `Expired`,
/// so blocking `BadSignature` here cannot reliably distinguish a forged or
/// expired certificate from a routine, valid one -- it only breaks the
/// verifier's intended purpose. `NotValidYet` is unaffected by this and
/// still reported correctly, since `rustls-webpki` checks the validity
/// window before attempting chain-building signature verification.
fn critical_verification_failure_no_real_trust_anchor<T>(
    verified_res: &Result<T, rustls::Error>,
) -> Option<rustls::Error> {
    if let Err(rustls::Error::InvalidCertificate(cert_err)) = verified_res {
        if matches!(
            cert_err,
            rustls::CertificateError::NotValidForName
                | rustls::CertificateError::NotValidYet
                | rustls::CertificateError::NotValidYetContext { .. }
        ) {
            return Some(rustls::Error::InvalidCertificate(cert_err.clone()));
        }
    }
    None
}

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

    // The certificate chain to be presented. The first certificate in the
    // vector must be the leaf certificate, containing the public key
    // corresponding to `key_asn1`. Subsequent certificates are intermediate CA
    // certificates, in order, up to the root.
    pub certs: Vec<CertificateDer<'static>>,
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

/// Provider trait that returns a trust anchor certificate.
/// Called each time a new session is created on the context.
pub trait TrustAnchorProvider: Send + Sync {
    fn get_trust_anchor(&self) -> Result<CertificateDer<'static>, ContextError>;
}

impl<F> TrustAnchorProvider for F
where
    F: Fn() -> Result<CertificateDer<'static>, ContextError> + Send + Sync,
{
    fn get_trust_anchor(&self) -> Result<CertificateDer<'static>, ContextError> {
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
    /// Optional trust anchor provider for the client.
    /// If set, client verification will be required.
    /// Called each time a new session is created.
    pub client_trust_anchor_provider: Option<Box<dyn TrustAnchorProvider>>,
    /// Optional custom certificate verifier. If provided, it will be called
    /// with the result of standard verification, allowing it to override
    /// failures or add additional checks.
    pub custom_cert_verifier: Option<Box<dyn CustomCertVerifier>>,
}

/// Parameters to configure OakSessionTlsClientContext for client behavior.
///
/// Server certificate verification is always enabled by default. If no
/// `server_trust_anchor_provider` is configured, standard certificate
/// verification will fail. In this case, a `custom_cert_verifier` must be
/// provided to perform validation or bypass standard verification checks.
pub struct ClientContextConfig {
    /// Optional trust anchor provider that can verify the server. If not set,
    /// standard WebPKI verification will fail, and a `custom_cert_verifier`
    /// must be provided to handle certificate validation.
    /// Called each time a new session is created.
    pub server_trust_anchor_provider: Option<Box<dyn TrustAnchorProvider>>,
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
    custom: Arc<dyn CustomCertVerifier>,
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

        if let Some(err) = critical_verification_failure(&verified_res) {
            return Err(err);
        }

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
    custom: Arc<dyn CustomCertVerifier>,
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

        if let Some(err) = critical_verification_failure(&verified_res) {
            return Err(err);
        }

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

/// A standalone server certificate verifier that delegates to a
/// [`CustomCertVerifier`] while still enforcing SAN verification.
///
/// Used when no trust anchors are configured but custom verification (such as
/// attestation-based checks) is desired.
#[derive(Debug)]
struct CustomOnlyServerCertVerifier {
    inner: Arc<dyn ServerCertVerifier>,
    custom: Arc<dyn CustomCertVerifier>,
}

impl ServerCertVerifier for CustomOnlyServerCertVerifier {
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

        if let Some(err) = critical_verification_failure_no_real_trust_anchor(&verified_res) {
            return Err(err);
        }

        let verify_result = verified_res.as_ref().map(|_| ());
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

/// A standalone client certificate verifier that delegates entirely to a
/// [`CustomCertVerifier`], without performing any standard WebPKI validation.
///
/// Used when no trust anchors are configured but custom verification (such as
/// attestation-based checks) is desired.
#[derive(Debug)]
struct CustomOnlyClientCertVerifier {
    custom: Arc<dyn CustomCertVerifier>,
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
    server_trust_anchor_provider: Option<Box<dyn TrustAnchorProvider>>,
    custom_cert_verifier: Option<Arc<dyn CustomCertVerifier>>,
    tls_identity_provider: Option<Box<dyn TlsIdentityProvider>>,
    server_name: String,
}

impl OakSessionTlsClientContext {
    /// Creates a new OakSessionTlsClientContext.
    pub fn create(config: ClientContextConfig) -> Result<Self, ContextError> {
        ensure_crypto_provider();

        let server_name =
            config.expected_server_name.unwrap_or_else(|| OAK_SESSION_TLS_SERVER_NAME.to_string());

        Ok(Self {
            server_trust_anchor_provider: config.server_trust_anchor_provider,
            custom_cert_verifier: config.custom_cert_verifier.map(Arc::from),
            tls_identity_provider: config.tls_identity_provider,
            server_name,
        })
    }

    /// Builds the server certificate verifier for a new session by resolving
    /// the trust anchor from the provider.
    fn build_verifier(
        &self,
    ) -> Result<Arc<dyn rustls::client::danger::ServerCertVerifier>, InitializationError> {
        let trust_anchor = self
            .server_trust_anchor_provider
            .as_ref()
            .map(|p| p.get_trust_anchor())
            .transpose()
            .map_err(|e| InitializationError::Tls(rustls::Error::General(e.to_string())))?;

        let verifier: Arc<dyn rustls::client::danger::ServerCertVerifier> =
            match (trust_anchor, &self.custom_cert_verifier) {
                (Some(trust_anchor), custom) => {
                    let mut root_store = RootCertStore::empty();
                    root_store.add(trust_anchor).map_err(|e| {
                        InitializationError::Tls(rustls::Error::General(e.to_string()))
                    })?;
                    let inner =
                        WebPkiServerVerifier::builder(Arc::new(root_store)).build().map_err(
                            |e| InitializationError::Tls(rustls::Error::General(e.to_string())),
                        )?;
                    if let Some(custom) = custom {
                        Arc::new(DelegatingServerCertVerifier { inner, custom: custom.clone() })
                    } else {
                        inner
                    }
                }
                (None, Some(custom)) => {
                    let dummy_cert =
                        rcgen::generate_simple_self_signed(vec!["dummy-root".to_string()])
                            .map_err(|e| {
                                InitializationError::Tls(rustls::Error::General(e.to_string()))
                            })?;
                    let cert_der = CertificateDer::from(dummy_cert.cert.der().to_vec());
                    let mut root_store = RootCertStore::empty();
                    root_store.add(cert_der).map_err(|e| {
                        InitializationError::Tls(rustls::Error::General(e.to_string()))
                    })?;
                    let inner =
                        WebPkiServerVerifier::builder(Arc::new(root_store)).build().map_err(
                            |e| InitializationError::Tls(rustls::Error::General(e.to_string())),
                        )?;
                    Arc::new(CustomOnlyServerCertVerifier { inner, custom: custom.clone() })
                }
                (None, None) => {
                    let root_store = RootCertStore::empty();
                    WebPkiServerVerifier::builder(Arc::new(root_store)).build().map_err(|e| {
                        InitializationError::Tls(rustls::Error::General(e.to_string()))
                    })?
                }
            };

        Ok(verifier)
    }

    /// Create a new OakSessionTlsInitializer for a new client session using
    /// this context's current configuration.
    ///
    /// Use this only if you need to drive the handshake yourself (e.g., for
    /// custom transport framing). For most use cases, prefer
    /// [`new_initialized_session`](Self::new_initialized_session) instead.
    pub fn new_session(&self) -> Result<OakSessionTlsInitializer, InitializationError> {
        let verifier = self.build_verifier()?;
        let builder =
            ClientConfig::builder().dangerous().with_custom_certificate_verifier(verifier);

        let mut client_config = if let Some(provider) = &self.tls_identity_provider {
            let identity = provider
                .get_identity()
                .map_err(|e| InitializationError::Tls(rustls::Error::General(e.to_string())))?;
            let certs = identity.certs;
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
    /// send/receive callbacks. Returns a tuple containing the initialized
    /// session (`OakSessionTls`) and any initial application-level
    /// plaintext data received during the handshake (`Vec<u8>`).
    ///
    /// This is the recommended API for most use cases.
    ///
    /// The returned `initial_data` (the second element of the tuple) contains
    /// any plaintext application data that was received and decrypted
    /// during the final flight of the handshake (for example, if the peer
    /// bundled their first application request with the final handshake
    /// message).
    ///
    /// **Important:**
    /// 1. The caller MUST check if `initial_data` is non-empty. If it is, this
    ///    data must be processed as the first received application message.
    ///    Because it has already been decrypted and extracted during the
    ///    handshake, it will NOT be returned by subsequent calls to
    ///    [`OakSessionTls::decrypt`]. Ignoring it can result in lost messages
    ///    or protocol hangs.
    /// 2. `initial_data` contains raw decrypted bytes from the transport
    ///    stream. It is **not** guaranteed to represent a complete,
    ///    deserializable message or a full protobuf. Its contents and framing
    ///    depend entirely on the application-level protocol. Feed these bytes
    ///    to the application's message framing or deserialization layer exactly
    ///    as if they had been read from the stream after the handshake.
    ///
    /// # Example
    /// ```ignore
    /// let (session, initial_data) = context.new_initialized_session(
    ///     |frame| async { socket.send(frame).await },
    ///     || async { socket.receive().await },
    /// ).await?;
    /// if !initial_data.is_empty() {
    ///     process_request(&initial_data);
    /// }
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
    client_trust_anchor_provider: Option<Box<dyn TrustAnchorProvider>>,
    custom_cert_verifier: Option<Arc<dyn CustomCertVerifier>>,
}

impl OakSessionTlsServerContext {
    /// Creates a new OakSessionTlsServerContext.
    pub fn create(config: ServerContextConfig) -> Result<Self, ContextError> {
        ensure_crypto_provider();

        Ok(Self {
            tls_identity_provider: config.tls_identity_provider,
            client_trust_anchor_provider: config.client_trust_anchor_provider,
            custom_cert_verifier: config.custom_cert_verifier.map(Arc::from),
        })
    }

    /// Create a new OakSessionTlsInitializer for a new server session using
    /// this context's current configuration.
    ///
    /// Use this only if you need to drive the handshake yourself (e.g., for
    /// custom transport framing). For most use cases, prefer
    /// [`new_initialized_session`](Self::new_initialized_session) instead.
    pub fn new_session(&self) -> Result<OakSessionTlsInitializer, InitializationError> {
        let client_verifier = self.build_client_verifier()?;
        let builder = if let Some(verifier) = client_verifier {
            ServerConfig::builder().with_client_cert_verifier(verifier)
        } else {
            ServerConfig::builder().with_no_client_auth()
        };

        let identity = self
            .tls_identity_provider
            .get_identity()
            .map_err(|e| InitializationError::Tls(rustls::Error::General(e.to_string())))?;
        let certs = identity.certs;
        let key = identity.key_der;

        let mut server_config =
            builder.with_single_cert(certs, key).map_err(InitializationError::Tls)?;

        server_config.alpn_protocols = vec![OAK_SESSION_TLS_ALPN_PROTOCOL.to_vec()];

        Ok(OakSessionTlsInitializer {
            who: "server".to_string(),
            connection: Connection::Server(ServerConnection::new(Arc::new(server_config))?),
        })
    }

    /// Builds the client certificate verifier for a new session by resolving
    /// the trust anchor from the provider.
    fn build_client_verifier(
        &self,
    ) -> Result<Option<Arc<dyn rustls::server::danger::ClientCertVerifier>>, InitializationError>
    {
        let trust_anchor = self
            .client_trust_anchor_provider
            .as_ref()
            .map(|p| p.get_trust_anchor())
            .transpose()
            .map_err(|e| InitializationError::Tls(rustls::Error::General(e.to_string())))?;

        let verifier: Option<Arc<dyn rustls::server::danger::ClientCertVerifier>> =
            match (trust_anchor, &self.custom_cert_verifier) {
                (Some(trust_anchor), custom) => {
                    let mut root_store = RootCertStore::empty();
                    root_store.add(trust_anchor).map_err(|e| {
                        InitializationError::Tls(rustls::Error::General(e.to_string()))
                    })?;
                    let inner =
                        WebPkiClientVerifier::builder(Arc::new(root_store)).build().map_err(
                            |e| InitializationError::Tls(rustls::Error::General(e.to_string())),
                        )?;
                    if let Some(custom) = custom {
                        Some(Arc::new(DelegatingClientCertVerifier {
                            inner,
                            custom: custom.clone(),
                        }))
                    } else {
                        Some(inner)
                    }
                }
                (None, Some(custom)) => {
                    Some(Arc::new(CustomOnlyClientCertVerifier { custom: custom.clone() }))
                }
                (None, None) => None,
            };

        Ok(verifier)
    }

    /// Create a new session and perform the TLS handshake using the provided
    /// send/receive callbacks. Returns a tuple containing the initialized
    /// session (`OakSessionTls`) and any initial application-level
    /// plaintext data received during the handshake (`Vec<u8>`).
    ///
    /// This is the recommended API for most use cases.
    ///
    /// The returned `initial_data` (the second element of the tuple) contains
    /// any plaintext application data that was received and decrypted
    /// during the final flight of the handshake (for example, if the peer
    /// bundled their first application request with the final handshake
    /// message).
    ///
    /// **Important:**
    /// 1. The caller MUST check if `initial_data` is non-empty. If it is, this
    ///    data must be processed as the first received application message.
    ///    Because it has already been decrypted and extracted during the
    ///    handshake, it will NOT be returned by subsequent calls to
    ///    [`OakSessionTls::decrypt`]. Ignoring it can result in lost messages
    ///    or protocol hangs.
    /// 2. `initial_data` contains raw decrypted bytes from the transport
    ///    stream. It is **not** guaranteed to represent a complete,
    ///    deserializable message or a full protobuf. Its contents and framing
    ///    depend entirely on the application-level protocol. Feed these bytes
    ///    to the application's message framing or deserialization layer exactly
    ///    as if they had been read from the stream after the handshake.
    ///
    /// # Example
    /// ```ignore
    /// let (session, initial_data) = context.new_initialized_session(
    ///     |frame| async { socket.send(frame).await },
    ///     || async { socket.receive().await },
    /// ).await?;
    /// if !initial_data.is_empty() {
    ///     process_request(&initial_data);
    /// }
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

    /// Consumes the initializer and returns the open Oak TLS session
    /// (`OakSessionTls`) and any initial application-level plaintext data
    /// received during the handshake (`Vec<u8>`).
    ///
    /// Returns an error if the handshake is not yet complete.
    ///
    /// The returned `initial_data` contains any plaintext application data that
    /// was received and decrypted during the final flight of the handshake.
    ///
    /// **Important:**
    /// 1. The caller MUST check if this returned data is non-empty and process
    ///    it before reading new frames. Because this data has already been
    ///    decrypted, it will not be returned by subsequent calls to
    ///    [`OakSessionTls::decrypt`].
    /// 2. This data is not guaranteed to represent a complete message or a full
    ///    deserializable proto. It contains raw decrypted bytes; format and
    ///    framing depend on the application-level protocol.
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
    ///
    /// Returns the open session and any initial application-level plaintext
    /// data received during the final flight of the handshake.
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

    use super::{
        ContextError, OAK_SESSION_TLS_SERVER_NAME, TlsIdentity, TlsIdentityProvider,
        TrustAnchorProvider,
    };

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
    /// key and certificate chain.
    pub fn create_static_cert_identity_provider(
        key_der: PrivateKeyDer<'static>,
        certs: Vec<CertificateDer<'static>>,
    ) -> Box<dyn TlsIdentityProvider> {
        // Clone the content to allow the closure to return them multiple times
        let key_der_bytes = key_der.secret_der().to_vec();
        let certs_bytes: Vec<Vec<u8>> = certs.iter().map(|c| c.as_ref().to_vec()).collect();

        Box::new(move || {
            let certs = certs_bytes.iter().map(|b| CertificateDer::from(b.clone())).collect();
            Ok(TlsIdentity {
                key_der: PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key_der_bytes.clone())),
                certs,
            })
        })
    }

    /// Creates a TrustAnchorProvider that always returns the provided static
    /// certificate.
    pub fn create_static_trust_anchor_provider(
        cert_der: CertificateDer<'static>,
    ) -> Box<dyn TrustAnchorProvider> {
        let bytes = cert_der.as_ref().to_vec();
        Box::new(move || Ok(CertificateDer::from(bytes.clone())))
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
                certs: vec![CertificateDer::from(cert_der_bytes.clone())],
            })
        }))
    }
}

#[cfg(test)]
mod critical_cert_verification_tests {
    //! Regression tests for the certificate-validation bypass: a
    //! `CustomCertVerifier` returning `Ok` must never be able to override a
    //! critical standard-verification failure (hostname mismatch, expiry,
    //! not-yet-valid, or a bad chain signature), only trust-anchor-only
    //! failures such as `UnknownIssuer`. Each test here fails if the fix in
    //! `critical_verification_failure` (and its three call sites) is
    //! reverted.

    use super::*;

    #[derive(Debug)]
    struct MockInnerServerVerifier {
        result: Result<(), rustls::Error>,
    }

    impl ServerCertVerifier for MockInnerServerVerifier {
        fn verify_server_cert(
            &self,
            _end_entity: &CertificateDer<'_>,
            _intermediates: &[CertificateDer<'_>],
            _server_name: &ServerName<'_>,
            _ocsp_response: &[u8],
            _now: UnixTime,
        ) -> Result<ServerCertVerified, rustls::Error> {
            self.result.clone().map(|_| ServerCertVerified::assertion())
        }
        fn verify_tls12_signature(
            &self,
            _m: &[u8],
            _c: &CertificateDer<'_>,
            _d: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, rustls::Error> {
            Ok(HandshakeSignatureValid::assertion())
        }
        fn verify_tls13_signature(
            &self,
            _m: &[u8],
            _c: &CertificateDer<'_>,
            _d: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, rustls::Error> {
            Ok(HandshakeSignatureValid::assertion())
        }
        fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
            vec![SignatureScheme::ED25519]
        }
    }

    #[derive(Debug)]
    struct MockInnerClientVerifier {
        result: Result<(), rustls::Error>,
    }

    impl ClientCertVerifier for MockInnerClientVerifier {
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
            _end_entity: &CertificateDer<'_>,
            _intermediates: &[CertificateDer<'_>],
            _now: UnixTime,
        ) -> Result<ClientCertVerified, rustls::Error> {
            self.result.clone().map(|_| ClientCertVerified::assertion())
        }
        fn verify_tls12_signature(
            &self,
            _m: &[u8],
            _c: &CertificateDer<'_>,
            _d: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, rustls::Error> {
            Ok(HandshakeSignatureValid::assertion())
        }
        fn verify_tls13_signature(
            &self,
            _m: &[u8],
            _c: &CertificateDer<'_>,
            _d: &DigitallySignedStruct,
        ) -> Result<HandshakeSignatureValid, rustls::Error> {
            Ok(HandshakeSignatureValid::assertion())
        }
        fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
            vec![SignatureScheme::ED25519]
        }
    }

    /// Mirrors `CustomCertVerifier`'s own documented, intended use: relax
    /// exactly one thing (here, always accept) regardless of the standard
    /// result it is handed.
    #[derive(Debug)]
    struct AlwaysAcceptCustomVerifier;

    impl CustomCertVerifier for AlwaysAcceptCustomVerifier {
        fn verify(
            &self,
            _end_entity: &CertificateDer<'_>,
            _intermediates: &[CertificateDer<'_>],
            _verify_result: Result<(), &rustls::Error>,
        ) -> Result<(), String> {
            Ok(())
        }
    }

    /// A custom verifier that always rejects, to confirm its own negative
    /// decision is still respected (this fix must not accidentally make
    /// custom rejection a no-op).
    #[derive(Debug)]
    struct AlwaysRejectCustomVerifier;

    impl CustomCertVerifier for AlwaysRejectCustomVerifier {
        fn verify(
            &self,
            _end_entity: &CertificateDer<'_>,
            _intermediates: &[CertificateDer<'_>],
            _verify_result: Result<(), &rustls::Error>,
        ) -> Result<(), String> {
            Err("rejected by custom verifier".to_string())
        }
    }

    fn dummy_cert() -> CertificateDer<'static> {
        CertificateDer::from(vec![0u8; 16])
    }

    fn dummy_server_name() -> ServerName<'static> {
        ServerName::try_from("example.com").unwrap()
    }

    fn delegating_server_verifier(
        result: Result<(), rustls::Error>,
        custom: Arc<dyn CustomCertVerifier>,
    ) -> DelegatingServerCertVerifier {
        DelegatingServerCertVerifier {
            inner: Arc::new(MockInnerServerVerifier { result }),
            custom,
        }
    }

    fn custom_only_server_verifier(
        result: Result<(), rustls::Error>,
        custom: Arc<dyn CustomCertVerifier>,
    ) -> CustomOnlyServerCertVerifier {
        CustomOnlyServerCertVerifier { inner: Arc::new(MockInnerServerVerifier { result }), custom }
    }

    fn delegating_client_verifier(
        result: Result<(), rustls::Error>,
        custom: Arc<dyn CustomCertVerifier>,
    ) -> DelegatingClientCertVerifier {
        DelegatingClientCertVerifier {
            inner: Arc::new(MockInnerClientVerifier { result }),
            custom,
        }
    }

    // --- DelegatingServerCertVerifier ---

    #[test]
    fn delegating_server_rejects_expired_even_when_custom_verifier_accepts() {
        let v = delegating_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::Expired)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err(), "an expired certificate must never be accepted by a custom verifier");
    }

    #[test]
    fn delegating_server_rejects_not_yet_valid_even_when_custom_verifier_accepts() {
        let v = delegating_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::NotValidYet)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err(), "a not-yet-valid certificate must never be accepted by a custom verifier");
    }

    #[test]
    fn delegating_server_rejects_bad_signature_even_when_custom_verifier_accepts() {
        let v = delegating_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::BadSignature)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err(), "a bad chain signature must never be accepted by a custom verifier");
    }

    #[test]
    fn delegating_server_rejects_hostname_mismatch_even_when_custom_verifier_accepts() {
        let v = delegating_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::NotValidForName)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err(), "a hostname mismatch must never be accepted by a custom verifier");
    }

    #[test]
    fn delegating_server_allows_unknown_issuer_override_when_custom_verifier_accepts() {
        let v = delegating_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::UnknownIssuer)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_ok(), "UnknownIssuer is the documented, intended override case");
    }

    #[test]
    fn delegating_server_accepts_valid_certificate() {
        let v = delegating_server_verifier(Ok(()), Arc::new(AlwaysAcceptCustomVerifier));
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_ok());
    }

    #[test]
    fn delegating_server_respects_custom_verifier_rejection_of_unknown_issuer() {
        let v = delegating_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::UnknownIssuer)),
            Arc::new(AlwaysRejectCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err(), "a custom verifier's own rejection must still be respected");
    }

    // --- CustomOnlyServerCertVerifier ---

    #[test]
    fn custom_only_server_rejects_not_yet_valid_even_when_custom_verifier_accepts() {
        let v = custom_only_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::NotValidYet)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err(), "a not-yet-valid certificate must never be accepted, even with no trust anchor configured");
    }

    #[test]
    fn custom_only_server_allows_expired_override_when_custom_verifier_accepts() {
        // Unlike DelegatingServerCertVerifier, this verifier's `inner` is
        // always checked against an arbitrary, unrelated dummy root (see
        // build_verifier's (None, Some(custom)) arm) -- there is no real
        // trust anchor here by design. A direct Expired result from `inner`
        // (which in practice is masked by BadSignature from the dummy-root
        // mismatch -- see the real-certificate integration test below) must
        // remain overridable, since the custom verifier is the entire trust
        // decision for this verifier, not an override of a real one.
        let v = custom_only_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::Expired)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_ok());
    }

    #[test]
    fn custom_only_server_allows_bad_signature_override_when_custom_verifier_accepts() {
        // BadSignature is the routine, expected result here: it is what a
        // certificate signed by any key other than the arbitrary dummy root
        // (i.e. every real certificate presented to this verifier) produces,
        // confirmed empirically against real rustls-webpki verification --
        // see custom_only_server_accepts_real_valid_self_signed_certificate
        // below, which is the regression test for the bug this test guards:
        // an earlier version of this fix blocked BadSignature here too,
        // which broke every legitimate use of this verifier.
        let v = custom_only_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::BadSignature)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_ok());
    }

    #[test]
    fn custom_only_server_rejects_hostname_mismatch_even_when_custom_verifier_accepts() {
        let v = custom_only_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::NotValidForName)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_err());
    }

    #[test]
    fn custom_only_server_allows_unknown_issuer_override_when_custom_verifier_accepts() {
        // This is the expected steady state for CustomOnlyServerCertVerifier:
        // no trust anchor is configured, so UnknownIssuer is the routine
        // result the custom (e.g. attestation-based) verifier is meant to
        // override.
        let v = custom_only_server_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::UnknownIssuer)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_server_cert(&dummy_cert(), &[], &dummy_server_name(), &[], UnixTime::now());
        assert!(r.is_ok());
    }

    // --- DelegatingClientCertVerifier (mTLS client-certificate path) ---

    #[test]
    fn delegating_client_rejects_expired_even_when_custom_verifier_accepts() {
        let v = delegating_client_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::Expired)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_client_cert(&dummy_cert(), &[], UnixTime::now());
        assert!(r.is_err(), "an expired client certificate must never be accepted by a custom verifier");
    }

    #[test]
    fn delegating_client_rejects_not_yet_valid_even_when_custom_verifier_accepts() {
        let v = delegating_client_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::NotValidYet)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_client_cert(&dummy_cert(), &[], UnixTime::now());
        assert!(r.is_err());
    }

    #[test]
    fn delegating_client_rejects_bad_signature_even_when_custom_verifier_accepts() {
        let v = delegating_client_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::BadSignature)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_client_cert(&dummy_cert(), &[], UnixTime::now());
        assert!(r.is_err(), "a bad chain signature on a client certificate must never be accepted by a custom verifier");
    }

    #[test]
    fn delegating_client_allows_unknown_issuer_override_when_custom_verifier_accepts() {
        let v = delegating_client_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::UnknownIssuer)),
            Arc::new(AlwaysAcceptCustomVerifier),
        );
        let r = v.verify_client_cert(&dummy_cert(), &[], UnixTime::now());
        assert!(r.is_ok(), "UnknownIssuer is the documented, intended override case for mTLS too");
    }

    #[test]
    fn delegating_client_accepts_valid_certificate() {
        let v = delegating_client_verifier(Ok(()), Arc::new(AlwaysAcceptCustomVerifier));
        let r = v.verify_client_cert(&dummy_cert(), &[], UnixTime::now());
        assert!(r.is_ok());
    }

    #[test]
    fn delegating_client_respects_custom_verifier_rejection_of_unknown_issuer() {
        let v = delegating_client_verifier(
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::UnknownIssuer)),
            Arc::new(AlwaysRejectCustomVerifier),
        );
        let r = v.verify_client_cert(&dummy_cert(), &[], UnixTime::now());
        assert!(r.is_err(), "a custom verifier's own rejection must still be respected for mTLS too");
    }

    // --- Real-certificate integration tests ---
    //
    // Everything above uses a mock `inner` verifier returning a fixed
    // result, which is precise for testing critical_verification_failure's
    // own logic but cannot catch a mismatch between what a mock returns and
    // what the *real* rustls-webpki verifier actually returns for a given
    // real certificate. This test exercises the real WebPkiServerVerifier,
    // built exactly as CustomOnlyServerCertVerifier's own build_verifier
    // constructs it (see the (None, Some(custom)) arm), against a genuinely
    // valid, non-expired, correctly-named self-signed certificate.
    //
    // This is the regression test for a real bug in an earlier version of
    // this fix: blocking BadSignature unconditionally broke every legitimate
    // use of CustomOnlyServerCertVerifier, because rustls-webpki reports
    // BadSignature -- not UnknownIssuer -- when a certificate's signature
    // doesn't match the arbitrary dummy root this verifier is built with,
    // which is true of every real certificate, valid or not.

    fn real_self_signed_cert(server_name: &str) -> CertificateDer<'static> {
        let params = rcgen::CertificateParams::new(vec![server_name.to_string()]).unwrap();
        let key_pair = rcgen::KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256).unwrap();
        let cert = params.self_signed(&key_pair).unwrap();
        CertificateDer::from(cert.der().to_vec())
    }

    #[test]
    fn custom_only_server_accepts_real_valid_self_signed_certificate() {
        // Mirrors build_verifier's (None, Some(custom)) arm exactly.
        let dummy_cert =
            rcgen::generate_simple_self_signed(vec!["dummy-root".to_string()]).unwrap();
        let dummy_cert_der = CertificateDer::from(dummy_cert.cert.der().to_vec());
        let mut root_store = RootCertStore::empty();
        root_store.add(dummy_cert_der).unwrap();
        let inner = WebPkiServerVerifier::builder(Arc::new(root_store)).build().unwrap();

        let v = CustomOnlyServerCertVerifier { inner, custom: Arc::new(AlwaysAcceptCustomVerifier) };

        let real_cert = real_self_signed_cert("my-service.example.com");
        let server_name = ServerName::try_from("my-service.example.com").unwrap();

        let r = v.verify_server_cert(&real_cert, &[], &server_name, &[], UnixTime::now());
        assert!(
            r.is_ok(),
            "a genuinely valid self-signed certificate must be accepted via the custom \
             verifier, exactly as CustomOnlyServerCertVerifier is documented to support: {r:?}"
        );
    }

    #[test]
    fn custom_only_server_hostname_mismatch_is_indistinguishable_from_a_match() {
        // This documents a real, pre-existing structural property of this
        // verifier discovered while fixing the bypass above, not a claim
        // about correct behavior: rustls-webpki's path-building fails the
        // chain-signature check against the arbitrary dummy root before it
        // ever reaches hostname verification, for every real certificate --
        // matched name or not. So `inner`'s result is BadSignature either
        // way, and this verifier has no signal from `inner` alone to tell
        // the two cases apart; hostname verification here depends entirely
        // on what the application's own CustomCertVerifier chooses to check
        // (it is handed `end_entity` and can parse the SAN itself). This is
        // not something introduced or fixable by this patch -- it is a
        // property of using a dummy root at all -- and is called out
        // separately for the maintainer's awareness.
        let dummy_cert =
            rcgen::generate_simple_self_signed(vec!["dummy-root".to_string()]).unwrap();
        let dummy_cert_der = CertificateDer::from(dummy_cert.cert.der().to_vec());
        let mut root_store = RootCertStore::empty();
        root_store.add(dummy_cert_der).unwrap();
        let inner = WebPkiServerVerifier::builder(Arc::new(root_store)).build().unwrap();

        let real_cert = real_self_signed_cert("my-service.example.com");
        let wrong_name = ServerName::try_from("someone-else.example.com").unwrap();
        let right_name = ServerName::try_from("my-service.example.com").unwrap();

        let mismatch_result = inner.verify_server_cert(&real_cert, &[], &wrong_name, &[], UnixTime::now());
        let match_result = inner.verify_server_cert(&real_cert, &[], &right_name, &[], UnixTime::now());

        assert!(matches!(
            mismatch_result,
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::BadSignature))
        ));
        assert!(matches!(
            match_result,
            Err(rustls::Error::InvalidCertificate(rustls::CertificateError::BadSignature))
        ));
    }
}
