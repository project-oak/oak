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

use log::info;
use openssl::{
    asn1::Asn1Time,
    bn::{BigNum, MsbOption},
    error::ErrorStack,
    hash::MessageDigest,
    nid::Nid,
    pkey::{PKey, Private},
    rsa::Rsa,
    x509::{
        extension::{AuthorityKeyIdentifier, BasicConstraints, KeyUsage, SubjectKeyIdentifier},
        X509Extension, X509NameBuilder, X509Req, X509,
    },
};

// X.509 certificate parameters.
// https://tools.ietf.org/html/rfc5280
const RSA_KEY_SIZE: u32 = 2048;
// Version is zero-indexed, so the value of `2` corresponds to the version `3`.
const CERTIFICATE_VERSION: i32 = 2;
// Length of the randomly generated X.509 certificate serial number (which is 20 bytes) excluding
// the most significant bit.
const SERIAL_NUMBER_SIZE: i32 = 159;
const CERTIFICATE_EXPIRATION_INTERVAL_IN_DAYS: u32 = 1;

/// Custom X.509 extension with a TEE application quote that was remotely attested by the Proxy
/// Attestation Service.
pub struct Quote {
    value: String,
}

impl Quote {
    pub fn new(value: &str) -> Self {
        Self {
            value: format!("Quote:{}", value.to_string()),
        }
    }

    /// Return the [`Quote`] extension as an [`X509Extension`].
    pub fn build(&self) -> Result<X509Extension, ErrorStack> {
        // Using [`Nid::NETSCAPE_COMMENT`] identifier since `rust-openssl` doesn't support custom
        // extensions yet:
        // https://github.com/sfackler/rust-openssl/issues/1411
        X509Extension::new_nid(None, None, Nid::NETSCAPE_COMMENT, &self.value)
    }
}

/// Convenience structure for creating X.509 certificates.
/// https://tools.ietf.org/html/rfc5280
pub struct CertificateAuthority {
    pub key_pair: PKey<Private>,
    pub root_certificate: X509,
}

impl CertificateAuthority {
    pub fn new() -> Self {
        let (key_pair, root_certificate) =
            Self::generate_root_certificate().expect("Couldn't generate root TLS certificate");
        Self {
            key_pair,
            root_certificate,
        }
    }

    /// Creates a root X.509 certificate and a corresponding private/public key pair.
    pub fn generate_root_certificate() -> anyhow::Result<(PKey<Private>, X509)> {
        info!("Generating root certificate");

        let rsa = Rsa::generate(RSA_KEY_SIZE)?;
        let key_pair = PKey::from_rsa(rsa)?;

        let mut name = X509NameBuilder::new()?;
        name.append_entry_by_text("O", "Oak")?;
        name.append_entry_by_text("CN", "Proxy Attestation Service")?;
        let name = name.build();

        let mut builder = X509::builder()?;
        builder.set_version(CERTIFICATE_VERSION)?;
        let serial_number = {
            let mut serial = BigNum::new()?;
            serial.rand(SERIAL_NUMBER_SIZE, MsbOption::MAYBE_ZERO, false)?;
            serial.to_asn1_integer()?
        };
        builder.set_serial_number(&serial_number)?;
        builder.set_subject_name(&name)?;
        builder.set_issuer_name(&name)?;
        builder.set_pubkey(&key_pair)?;
        let not_before = Asn1Time::days_from_now(0)?;
        builder.set_not_before(&not_before)?;
        let not_after = Asn1Time::days_from_now(CERTIFICATE_EXPIRATION_INTERVAL_IN_DAYS)?;
        builder.set_not_after(&not_after)?;

        builder.append_extension(BasicConstraints::new().critical().ca().build()?)?;
        builder.append_extension(
            KeyUsage::new()
                .critical()
                .key_cert_sign()
                .crl_sign()
                .build()?,
        )?;

        let subject_key_identifier =
            SubjectKeyIdentifier::new().build(&builder.x509v3_context(None, None))?;
        builder.append_extension(subject_key_identifier)?;

        builder.sign(&key_pair, MessageDigest::sha256())?;
        let certificate = builder.build();

        Ok((key_pair, certificate))
    }

    /// Create an X509 certificate based on the certificate signing `request`.
    pub fn sign_certificate(&self, request: X509Req, tee_quote: &str) -> anyhow::Result<X509> {
        info!("Signing certificate");

        let mut builder = X509::builder()?;
        builder.set_version(2)?;
        let serial_number = {
            let mut serial = BigNum::new()?;
            serial.rand(159, MsbOption::MAYBE_ZERO, false)?;
            serial.to_asn1_integer()?
        };
        builder.set_serial_number(&serial_number)?;
        builder.set_subject_name(request.subject_name())?;
        builder.set_issuer_name(self.root_certificate.subject_name())?;
        builder.set_pubkey(&request.public_key()?.as_ref())?;
        let not_before = Asn1Time::days_from_now(0)?;
        builder.set_not_before(&not_before)?;
        let not_after = Asn1Time::days_from_now(365)?;
        builder.set_not_after(&not_after)?;

        builder.append_extension(BasicConstraints::new().build()?)?;

        builder.append_extension(
            KeyUsage::new()
                .critical()
                .non_repudiation()
                .digital_signature()
                .key_encipherment()
                .build()?,
        )?;

        let subject_key_identifier = SubjectKeyIdentifier::new()
            .build(&builder.x509v3_context(Some(&self.root_certificate), None))?;
        builder.append_extension(subject_key_identifier)?;

        let auth_key_identifier = AuthorityKeyIdentifier::new()
            .keyid(false)
            .issuer(false)
            .build(&builder.x509v3_context(Some(&self.root_certificate), None))?;
        builder.append_extension(auth_key_identifier)?;

        // Add X.509 extensions from the certificate signing request.
        for extension in request.extensions()?.iter() {
            builder.append_extension2(extension)?;
        }

        let tee_quote_extension = Quote::new(tee_quote).build()?;
        builder.append_extension(tee_quote_extension)?;

        builder.sign(&self.key_pair, MessageDigest::sha256())?;
        let certificate = builder.build();

        Ok(certificate)
    }
}
