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

use anyhow::Context;
use http::uri::Uri;
use log::info;
use oak_proxy_attestation::proto::{
    proxy_attestation_client::ProxyAttestationClient, GetSignedCertificateRequest,
};
use openssl::{
    hash::MessageDigest,
    pkey::{PKey, Private},
    rsa::Rsa,
    x509::{X509NameBuilder, X509ReqBuilder},
};
use tonic::{
    transport::{Certificate, Channel, ClientTlsConfig, Identity},
    Request,
};

const RSA_KEY_SIZE: u32 = 2048;

/// Creates an X.509 certificate signing request and sends it to the Proxy Attestation Service.
/// After receiving back a signed certificate, creates TLS [`Identity`].
pub async fn get_tls_identity_from_proxy(
    uri: &Uri,
    root_tls_certificate: &[u8],
) -> anyhow::Result<Identity> {
    // Create certificate signing request and a corresponding private/public key pair.
    let rsa_key_pair = Rsa::generate(RSA_KEY_SIZE)?;
    let private_key = rsa_key_pair.private_key_to_pem()?.to_vec();
    let key_pair = PKey::from_rsa(rsa_key_pair)?;
    let certificate_request = create_certificate_request(&key_pair)?;

    // Request a signed certificate from the Proxy Attestation Service.
    info!(
        "Sending certificate signing request to Proxy Attestation Service: {:?}",
        uri
    );
    let mut client = create_proxy_client(&uri, &root_tls_certificate)
        .await
        .context("Couldn't create gRPC client")?;
    let request = Request::new(GetSignedCertificateRequest {
        certificate_request,
    });
    let response = client
        .get_signed_certificate(request)
        .await
        .context("Couldn't get signed certificate")?;
    let certificate = response.get_ref().certificate.to_vec();
    info!("Received signed certificate from Proxy Attestation Service");

    Ok(Identity::from_pem(&certificate, &private_key))
}

/// Creates an X.509 certificate signing request.
/// https://tools.ietf.org/html/rfc5280
///
/// TODO(#1869): Load certificate signing request from a PEM file.
fn create_certificate_request(key_pair: &PKey<Private>) -> anyhow::Result<Vec<u8>> {
    let mut builder = X509ReqBuilder::new()?;
    builder.set_pubkey(&key_pair)?;

    let mut name = X509NameBuilder::new()?;
    name.append_entry_by_text("O", "Oak")?;
    name.append_entry_by_text("CN", "Example Application")?;
    let name = name.build();
    builder.set_subject_name(&name)?;

    use openssl::{stack::Stack, x509::extension::SubjectAlternativeName};
    let mut extensions = Stack::new()?;
    let subject_alt_name = SubjectAlternativeName::new()
        .dns("project-oak.local")
        .dns("localhost")
        .ip("127.0.0.1")
        .ip("::1")
        .build(&builder.x509v3_context(None))?;
    extensions.push(subject_alt_name)?;
    builder.add_extensions(&extensions)?;

    builder.sign(&key_pair, MessageDigest::sha256())?;
    let request = builder.build();
    request
        .to_pem()
        .context("Couldn't create PEM encoded certificate request")
}

/// Creates TLS client for connecting to the Proxy Attestation Service.
async fn create_proxy_client(
    uri: &Uri,
    root_tls_certificate: &[u8],
) -> anyhow::Result<ProxyAttestationClient<Channel>> {
    let tls_config =
        ClientTlsConfig::new().ca_certificate(Certificate::from_pem(root_tls_certificate.to_vec()));
    let channel = Channel::builder(uri.clone())
        .tls_config(tls_config)
        .context("Couldn't create TLS configuration")?
        .connect()
        .await
        .context("Couldn't connect to Oak Application")?;
    Ok(ProxyAttestationClient::new(channel))
}
