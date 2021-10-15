//
// Copyright 2021 The Project Oak Authors
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

use anyhow::{anyhow, Context};
use http::uri::Uri;
use log::{debug, warn};
use oak_attestation_common::{
    get_sha256,
    report::{AttestationInfo, TEE_EXTENSION_OID},
};
use tokio_rustls::{
    rustls::{self, ServerCertVerifier},
    webpki::DNSNameRef,
};
use tonic::transport::{Channel, ClientTlsConfig};
use x509_parser::{der_parser::der::parse_der, parse_x509_certificate};

/// Creates a gRPC channel to a TEE service specified by [`uri`] that checks that:
/// - TLS certificate was signed by the [`root_tls_certificate`] of the Proxy Attestation Service.
/// - X.509 TEE extension contains a TEE report with expected [`tee_measurement`].
pub async fn create_attested_grpc_channel(
    uri: &Uri,
    root_tls_certificate: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<Channel> {
    let tls_config = {
        let config = create_tls_attestation_config(root_tls_certificate, tee_measurement)
            .context("Couldn't create TLS config")?;
        ClientTlsConfig::new().rustls_client_config(config)
    };
    Channel::builder(uri.clone())
        .tls_config(tls_config)
        .context("Couldn't create TLS configuration")?
        .connect()
        .await
        .context("Couldn't connect to Oak Application")
}

/// Creates an HTTPS client which checks that X.509 TEE extension contains a TEE report with the
/// expected [`tee_measurement`] and a hash of the public key used to the TLS certificate.
pub async fn create_attested_https_client(
    tee_measurement: &[u8],
) -> anyhow::Result<hyper::Client<hyper_rustls::HttpsConnector<hyper::client::HttpConnector>>> {
    // Config doesn't need root certificates, since it accepts self-signed ones.
    let tls_config = create_tls_attestation_config(&[], tee_measurement)
        .context("Couldn't create TLS config")?;

    let mut http = hyper::client::HttpConnector::new();
    // Enable HTTPS by allowing Uri`s to have the `https` scheme.
    http.enforce_http(false);
    let https = hyper_rustls::HttpsConnector::from((http, tls_config));
    let client: hyper::client::Client<_, hyper::Body> =
        hyper::client::Client::builder().build(https);

    Ok(client)
}

/// Creates client TLS configuration with a custom X.509 certificate verifier.
/// The verifier also checks that the `tee_measurement` is the same as the TEE measurement included
/// in the certificate.
/// [`root_tls_certificate`] should contain only a single PEM encoded certificate.
/// https://tools.ietf.org/html/rfc1421
pub fn create_tls_attestation_config(
    root_tls_certificate: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<rustls::ClientConfig> {
    let mut config = rustls::ClientConfig::new();

    // Configure ALPN to accept HTTP/1.1 and HTTP/2.
    // https://tools.ietf.org/html/rfc7639
    config.set_protocols(&[b"http/1.1".to_vec(), b"h2".to_vec()]);

    // Add root TLS certificate.
    let mut cc_reader = std::io::BufReader::new(&root_tls_certificate[..]);
    let certs = rustls::internal::pemfile::certs(&mut cc_reader)
        .map_err(|error| anyhow!("Couldn't parse TLS certificate: {:?}", error))?;
    for certificate in certs.iter() {
        config
            .root_store
            .add(certificate)
            .context("Couldn't add root certificate")?;
    }

    // Set custom X.509 certificate verifier.
    config
        .dangerous()
        // [`rustls::DangerousClientConfig::set_certificate_verifier`] completely overwrites the
        // default verifier.
        // https://docs.rs/rustls/0.19.0/rustls/struct.DangerousClientConfig.html#impl
        .set_certificate_verifier(std::sync::Arc::new(RemoteAttestationVerifier::new(
            tee_measurement,
        )));
    Ok(config)
}

/// Custom X.509 certificate verifier that checks TEE reports in the X.509 TEE extension.
struct RemoteAttestationVerifier {
    tee_measurement: Vec<u8>,
}

impl RemoteAttestationVerifier {
    fn new(tee_measurement: &[u8]) -> Self {
        Self {
            tee_measurement: tee_measurement.to_vec(),
        }
    }
}

impl rustls::ServerCertVerifier for RemoteAttestationVerifier {
    fn verify_server_cert(
        &self,
        root_certificates: &rustls::RootCertStore,
        certificates: &[rustls::Certificate],
        hostname: DNSNameRef,
        ocsp: &[u8],
    ) -> Result<rustls::ServerCertVerified, rustls::TLSError> {
        // Client expects a single certificate corresponding to remote attestation.
        for certificate in certificates.iter() {
            verify_certificate(certificate, root_certificates, hostname, ocsp).map_err(
                |error| {
                    let error =
                        rustls::TLSError::General(format!("Certificate is not valid: {:?}", error));
                    warn!("{:?}", error);
                    error
                },
            )?;

            verify_attestation(certificate, &self.tee_measurement).map_err(|error| {
                let error = rustls::TLSError::General(format!(
                    "Remote attestation is not valid: {:?}",
                    error
                ));
                warn!("{:?}", error);
                error
            })?;
        }

        Ok(rustls::ServerCertVerified::assertion())
    }
}

/// Verifies certificate correctness using [`WebPKIVerifier`].
fn verify_certificate(
    certificate: &rustls::Certificate,
    root_certificates: &rustls::RootCertStore,
    hostname: DNSNameRef,
    ocsp: &[u8],
) -> anyhow::Result<()> {
    // This check is required since [`rustls::DangerousClientConfig::set_certificate_verifier`]
    // completely overwrites the default verifier.
    // https://docs.rs/rustls/0.19.0/rustls/struct.DangerousClientConfig.html#impl
    let verifier = rustls::WebPKIVerifier::new();
    if root_certificates.is_empty() {
        // Verify self-signed certificate validity using the certificate as it's own root
        // certificate.
        let mut root_certificates = rustls::RootCertStore::empty();
        root_certificates
            .add(certificate)
            .context("Malformed certificate")?;
        verifier
            .verify_server_cert(&root_certificates, &[certificate.clone()], hostname, ocsp)
            .context("Self-signed certificate is not valid")?;
    } else {
        verifier
            .verify_server_cert(root_certificates, &[certificate.clone()], hostname, ocsp)
            .context("Certificate is not valid")?;
    }

    Ok(())
}

/// Verifies remote attestation:
/// - Checks that the TEE report is signed by TEE firmware Provider’s root key
///   - The corresponding TEE Provider’s certificate is sent alongside the TEE report
/// - Checks that the public key hash from the TEE report is equal to the hash of the public key
///   presented in the self-signed X.509 certificate
/// - Extracts the TEE measurement from the TEE report and compares it to the expected one
fn verify_attestation(
    certificate: &rustls::Certificate,
    tee_measurement: &[u8],
) -> anyhow::Result<()> {
    // Parse X.509 certificate encoded using DER format.
    // https://tools.ietf.org/html/rfc7468
    let (_, parsed_certificate) =
        parse_x509_certificate(&certificate.0).context("Couldn't parse certificate")?;

    // Extract public key.
    let parsed_openssl_certificate =
        openssl::x509::X509::from_der(&certificate.0).context("Couldn't parse certificate")?;
    let public_key = parsed_openssl_certificate
        .public_key()
        .context("Couldn't extract public key")?
        .public_key_to_der()
        .context("Couldn't convert public key to PEM")?;

    // Extract X.509 TEE extension.
    let extensions = parsed_certificate.extensions();
    debug!("Provided X.509 extension: {:?}", extensions);
    let tee_extension = extensions
        .iter()
        .find(|&ext| ext.oid == TEE_EXTENSION_OID)
        .ok_or_else(|| anyhow!("Couldn't find X.509 TEE extension"))?;
    let tee_extension_value = parse_der(tee_extension.value)
        .context("Couldn't parse X.509 TEE extension")?
        .1
        .as_str()
        .context("Couldn't convert TEE extension to string")?;
    debug!(
        "Found TEE X.509 extension: {:?}, {:?}",
        TEE_EXTENSION_OID, tee_extension_value
    );

    // Check that X.509 TEE extension contains a correct TEE report.
    verify_tee_extension(tee_extension_value, &public_key, tee_measurement)
        .context("Incorrect TEE extension")?;

    Ok(())
}

/// Verifies X.509 TEE extension:
/// - Checks that the extension contains a TEE report and a SHA-256 digest of the [`public_key`].
/// - Checks that the TEE report is signed by TEE firmware Provider’s root key
/// - Also checks the correctness of the TEE measurement from the TEE report, i.e. checks that it's
///   equal to the [`tee_measurement`].
fn verify_tee_extension(
    extension: &str,
    public_key: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<()> {
    let public_key_hash = get_sha256(public_key);

    // Attestation info is encoded using JSON.
    let attestation_info =
        AttestationInfo::from_string(extension).context("Couldn't parse attestation info")?;

    debug!("Expected public key hash: {:?}", public_key_hash);
    debug!(
        "Received public key hash: {:?}",
        attestation_info.report.data
    );
    if public_key_hash != attestation_info.report.data {
        return Err(anyhow!("TEE report contains incorrect public key"));
    }
    debug!("Expected TEE measurement: {:?}", tee_measurement);
    debug!(
        "Received TEE measurement: {:?}",
        attestation_info.report.measurement
    );
    if tee_measurement != attestation_info.report.measurement {
        return Err(anyhow!("TEE report contains incorrect TEE measurements"));
    }
    verify_tee_report_signature(&attestation_info)
        .context("TEE report contains incorrect signature")?;
    Ok(())
}

/// Verifies that the TEE report is signed by TEE firmware Provider’s root key.
fn verify_tee_report_signature(_attestation_info: &AttestationInfo) -> anyhow::Result<()> {
    // Placeholder for verifying TEE report's signature.
    // TODO(#1867): Add remote attestation support.
    Ok(())
}
