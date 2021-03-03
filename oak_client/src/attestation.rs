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
use oak_attestation_common::{Report, TEE_EXTENSION_OID};
use tokio_rustls::rustls;
use tonic::transport::{Channel, ClientTlsConfig};
use x509_parser::{der_parser::der::parse_der, parse_x509_certificate};

/// Creates a remotely attested TLS channel for connecting to Oak.
pub async fn create_attested_tls_channel(
    uri: &Uri,
    root_tls_certificate: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<Channel> {
    let tls_config = create_tls_attestation_config(root_tls_certificate, tee_measurement)
        .context("Couldn't create TLS config")?;
    Channel::builder(uri.clone())
        .tls_config(tls_config)
        .context("Couldn't create TLS configuration")?
        .connect()
        .await
        .context("Couldn't connect to Oak Application")
}
/// Create client TLS configuration with a custom X.509 certificate verifier.
/// [`root_tls_certificate`] should contain only a single PEM encoded certificate.
/// https://tools.ietf.org/html/rfc1421
pub fn create_tls_attestation_config(
    root_tls_certificate: &[u8],
    tee_measurement: &[u8],
) -> anyhow::Result<ClientTlsConfig> {
    let mut config = rustls::ClientConfig::new();

    // Configure ALPN to accept HTTP/2.
    // https://tools.ietf.org/html/rfc7639
    config.set_protocols(&[b"h2".to_vec()]);

    // Add root TLS certificate.
    let mut cc_reader = std::io::BufReader::new(&root_tls_certificate[..]);
    let certs = rustls::internal::pemfile::certs(&mut cc_reader)
        .map_err(|error| anyhow!("Couldn't parse TLS certificate: {:?}", error))?;
    // Only the Proxy Attestation root certificate is required.
    if certs.len() != 1 {
        return Err(anyhow!(
            "Only a single PEM certificate must be provided, provided {}",
            certs.len()
        ));
    }
    config
        .root_store
        .add(&certs[0])
        .context("Couldn't add root certificate")?;

    // Set custom X.509 certificate verifier.
    config
        .dangerous()
        // [`rustls::DangerousClientConfig::set_certificate_verifier`] completely overwrites the
        // default verifier.
        // https://docs.rs/rustls/0.19.0/rustls/struct.DangerousClientConfig.html#impl
        .set_certificate_verifier(std::sync::Arc::new(RemoteAttestationVerifier::new(
            tee_measurement,
        )));

    Ok(ClientTlsConfig::new().rustls_client_config(config))
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

    fn check_tee_report(&self, extension: &str) -> anyhow::Result<()> {
        let tee_report = Report::from_string(extension).context("Couldn't parse TEE report")?;
        if self.tee_measurement == tee_report.measurement {
            Ok(())
        } else {
            Err(anyhow!("Incorrect TEE report"))
        }
    }
}

impl rustls::ServerCertVerifier for RemoteAttestationVerifier {
    fn verify_server_cert(
        &self,
        roots: &rustls::RootCertStore,
        certs: &[rustls::Certificate],
        hostname: webpki::DNSNameRef,
        ocsp: &[u8],
    ) -> Result<rustls::ServerCertVerified, rustls::TLSError> {
        // Only a certificate created by the Attestation Proxy is required.
        if certs.len() != 1 {
            return Err(rustls::TLSError::General(format!(
                "Only a single certificate must be provided, provided {}",
                certs.len()
            )));
        }
        let certificate = &certs[0].0;

        // Parse X.509 certificate encoded using DER format.
        // https://tools.ietf.org/html/rfc7468
        let (_, parsed_certificate) = parse_x509_certificate(&certificate).map_err(|error| {
            rustls::TLSError::General(format!("Couldn't parse certificate: {}", error))
        })?;

        // Extract X.509 TEE extension.
        let extensions = parsed_certificate.extensions();
        let tee_extension = extensions.get(&TEE_EXTENSION_OID).ok_or_else(|| {
            rustls::TLSError::General("Couldn't find X.509 TEE extension".to_string())
        })?;
        let tee_extension_value = parse_der(tee_extension.value)
            .map_err(|error| {
                rustls::TLSError::General(format!(
                    "Couldn't parse X.509 TEE extension: {:?}",
                    error
                ))
            })?
            .1
            .as_str()
            .map_err(|error| {
                rustls::TLSError::General(format!("Couldn't parse TEE report value: {:?}", error))
            })?;

        // Check that X.509 TEE extension contains a correct TEE report.
        self.check_tee_report(tee_extension_value)
            .map_err(|error| {
                rustls::TLSError::General(format!("Incorrect TEE report: {:?}", error))
            })?;

        // Use [`rustls::WebPKIVerifier`] to check certificate correctness.
        // This check is required since [`rustls::DangerousClientConfig::set_certificate_verifier`]
        // completely overwrites the default verifier.
        // https://docs.rs/rustls/0.19.0/rustls/struct.DangerousClientConfig.html#impl
        let verifier = rustls::WebPKIVerifier::new();
        verifier.verify_server_cert(roots, certs, hostname, ocsp)
    }
}
