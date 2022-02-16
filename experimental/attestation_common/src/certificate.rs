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

use crate::{
    get_sha256,
    report::{AttestationInfo, Report},
};
use anyhow::Context;
use log::info;
use openssl::{
    asn1::Asn1Time,
    bn::{BigNum, MsbOption},
    hash::MessageDigest,
    pkey::{HasPublic, PKey, PKeyRef, Private},
    rsa::Rsa,
    stack::Stack,
    x509::{
        extension::{
            AuthorityKeyIdentifier, BasicConstraints, KeyUsage, SubjectAlternativeName,
            SubjectKeyIdentifier,
        },
        X509Builder, X509NameBuilder, X509Ref, X509Req, X509,
    },
};

// X.509 certificate parameters.
//
// <https://tools.ietf.org/html/rfc5280>
const RSA_KEY_SIZE: u32 = 2048;
// Version is zero-indexed, so the value of `2` corresponds to the version `3`.
const CERTIFICATE_VERSION: i32 = 2;
// Length of the randomly generated X.509 certificate serial number (which is 20 bytes).
//
// The most significant bit is excluded because it's passed as a separate argument to:
// https://docs.rs/openssl/0.10.33/openssl/bn/struct.BigNum.html#method.rand
const SERIAL_NUMBER_SIZE: i32 = 159;
const CERTIFICATE_EXPIRATION_INTERVAL_IN_DAYS: u32 = 1;
const DEFAULT_DNS_NAME: &str = "localhost";

/// Indicates whether to add a custom TEE extension to a certificate.
#[derive(PartialEq)]
pub enum AddTeeExtension {
    /// Enum value contains a PEM encoded TEE Provider's X.509 certificate that signs TEE firmware
    /// key.
    Yes(Vec<u8>),
    No,
}

/// Convenience structure for generating X.509 certificates.
///
/// <https://tools.ietf.org/html/rfc5280>
pub struct CertificateAuthority {
    pub key_pair: PKey<Private>,
    pub root_certificate: X509,
}

impl CertificateAuthority {
    /// Generates a root X.509 certificate and a corresponding private/public key pair.
    ///
    /// `add_tee_extension` indicates whether to add a custom extension containing a TEE report to
    /// the root certificate.
    pub fn create(add_tee_extension: AddTeeExtension) -> anyhow::Result<Self> {
        let key_pair = CertificateAuthority::generate_key_pair()?;
        let root_certificate =
            CertificateAuthority::generate_root_certificate(&key_pair, add_tee_extension)?;
        Ok(Self {
            key_pair,
            root_certificate,
        })
    }

    /// Generates RSA private/public key pair.
    fn generate_key_pair() -> anyhow::Result<PKey<Private>> {
        let rsa = Rsa::generate(RSA_KEY_SIZE).context("Couldn't generate RSA key")?;
        PKey::from_rsa(rsa).context("Couldn't parse RSA key")
    }

    /// Creates a root X.509 certificate.
    fn generate_root_certificate(
        key_pair: &PKey<Private>,
        add_tee_extension: AddTeeExtension,
    ) -> anyhow::Result<X509> {
        info!("Generating root certificate");

        let mut builder = CertificateBuilder::create()?;
        builder.set_version(CERTIFICATE_VERSION)?;
        builder.set_serial_number(SERIAL_NUMBER_SIZE)?;
        builder.set_name()?;
        builder.set_public_key(key_pair)?;
        builder.set_expiration_interval(CERTIFICATE_EXPIRATION_INTERVAL_IN_DAYS)?;

        builder.add_basic_constraints_extension(true)?;
        builder.add_key_usage_extension(true)?;
        builder.add_subject_key_identifier_extension(None)?;
        builder.add_subject_alt_name_extension()?;

        // Bind the certificate to the TEE firmware using an X.509 TEE extension.
        if let AddTeeExtension::Yes(tee_certificate) = add_tee_extension {
            builder.add_tee_extension(key_pair, tee_certificate)?;
        }

        let certificate = builder.build(key_pair)?;
        Ok(certificate)
    }

    /// Generates an X.509 certificate based on the certificate signing `request`.
    ///
    /// `add_tee_extension` indicates whether to add a custom extension containing a TEE report.
    pub fn sign_certificate(
        &self,
        request: X509Req,
        add_tee_extension: AddTeeExtension,
    ) -> anyhow::Result<X509> {
        info!("Signing certificate");

        let mut builder = CertificateBuilder::create()?;
        builder.set_version(CERTIFICATE_VERSION)?;
        builder.set_serial_number(SERIAL_NUMBER_SIZE)?;
        builder.set_name()?;
        builder.set_public_key(request.public_key()?.as_ref())?;
        builder.set_expiration_interval(CERTIFICATE_EXPIRATION_INTERVAL_IN_DAYS)?;

        builder.add_basic_constraints_extension(false)?;
        builder.add_key_usage_extension(false)?;
        builder.add_subject_key_identifier_extension(Some(&self.root_certificate))?;
        builder.add_auth_key_identifier_extension(&self.root_certificate)?;

        // Add X.509 extensions from the certificate signing request.
        builder.add_extensions(request.extensions()?)?;

        // Bind the certificate to the TEE firmware using an X.509 TEE extension.
        if let AddTeeExtension::Yes(tee_certificate) = add_tee_extension {
            builder.add_tee_extension(request.public_key()?.as_ref(), tee_certificate)?;
        }

        let certificate = builder.build(&self.key_pair)?;
        Ok(certificate)
    }

    /// Get RSA key pair encoded in PEM format.
    ///
    /// <https://tools.ietf.org/html/rfc7468>
    pub fn get_private_key_pem(&self) -> anyhow::Result<Vec<u8>> {
        self.key_pair
            .private_key_to_pem_pkcs8()
            .context("Couldn't encode key pair in PEM format")
    }

    /// Get a root X.509 certificate encoded in PEM format.
    ///
    /// <https://tools.ietf.org/html/rfc7468>
    pub fn get_root_certificate_pem(&self) -> anyhow::Result<Vec<u8>> {
        self.root_certificate
            .to_pem()
            .context("Couldn't encode root certificate in PEM format")
    }
}

/// Helper struct that implements certificate creation using `openssl`.
struct CertificateBuilder {
    builder: X509Builder,
}

impl CertificateBuilder {
    fn create() -> anyhow::Result<Self> {
        let builder = X509::builder()?;
        Ok(Self { builder })
    }

    fn set_version(&mut self, version: i32) -> anyhow::Result<&mut Self> {
        self.builder.set_version(version)?;
        Ok(self)
    }

    fn set_serial_number(&mut self, serial_number_size: i32) -> anyhow::Result<&mut Self> {
        let serial_number = {
            let mut serial = BigNum::new()?;
            serial.rand(serial_number_size, MsbOption::MAYBE_ZERO, false)?;
            serial.to_asn1_integer()?
        };
        self.builder.set_serial_number(&serial_number)?;
        Ok(self)
    }

    fn set_name(&mut self) -> anyhow::Result<&mut Self> {
        let mut name = X509NameBuilder::new()?;
        name.append_entry_by_text("O", "Oak")?;
        name.append_entry_by_text("CN", "Proxy Attestation Service")?;
        let name = name.build();

        self.builder.set_subject_name(&name)?;
        self.builder.set_issuer_name(&name)?;

        Ok(self)
    }

    fn set_public_key<T>(&mut self, public_key: &PKeyRef<T>) -> anyhow::Result<&mut Self>
    where
        T: HasPublic,
    {
        self.builder.set_pubkey(public_key)?;
        Ok(self)
    }

    fn set_expiration_interval(&mut self, expiration_interval: u32) -> anyhow::Result<&mut Self> {
        let not_before = Asn1Time::days_from_now(0)?;
        self.builder.set_not_before(&not_before)?;
        let not_after = Asn1Time::days_from_now(expiration_interval)?;
        self.builder.set_not_after(&not_after)?;

        Ok(self)
    }

    fn add_basic_constraints_extension(&mut self, is_critical: bool) -> anyhow::Result<&mut Self> {
        if is_critical {
            self.builder
                .append_extension(BasicConstraints::new().critical().build()?)?;
        } else {
            self.builder
                .append_extension(BasicConstraints::new().build()?)?;
        }
        Ok(self)
    }

    fn add_key_usage_extension(&mut self, is_root_certificate: bool) -> anyhow::Result<&mut Self> {
        if is_root_certificate {
            self.builder.append_extension(
                KeyUsage::new()
                    .critical()
                    .key_cert_sign()
                    .crl_sign()
                    .build()?,
            )?;
        } else {
            self.builder.append_extension(
                KeyUsage::new()
                    .critical()
                    .non_repudiation()
                    .digital_signature()
                    .key_encipherment()
                    .build()?,
            )?;
        }
        Ok(self)
    }

    fn add_subject_key_identifier_extension(
        &mut self,
        root_certificate: Option<&X509Ref>,
    ) -> anyhow::Result<&mut Self> {
        let subject_key_identifier = SubjectKeyIdentifier::new()
            .build(&self.builder.x509v3_context(root_certificate, None))?;
        self.builder.append_extension(subject_key_identifier)?;
        Ok(self)
    }

    fn add_subject_alt_name_extension(&mut self) -> anyhow::Result<&mut Self> {
        let subject_alt_name = SubjectAlternativeName::new()
            .dns(DEFAULT_DNS_NAME)
            .build(&self.builder.x509v3_context(None, None))?;
        self.builder.append_extension(subject_alt_name)?;
        Ok(self)
    }

    fn add_auth_key_identifier_extension(
        &mut self,
        root_certificate: &X509Ref,
    ) -> anyhow::Result<&mut Self> {
        let auth_key_identifier = AuthorityKeyIdentifier::new()
            .keyid(false)
            .issuer(false)
            .build(&self.builder.x509v3_context(Some(root_certificate), None))?;
        self.builder.append_extension(auth_key_identifier)?;
        Ok(self)
    }

    // Generates a TEE report with the public key hash as data and add it to the certificate as a
    // custom extension. This is required to bind the certificate to the TEE firmware.
    fn add_tee_extension<T>(
        &mut self,
        public_key: &PKeyRef<T>,
        tee_certificate: Vec<u8>,
    ) -> anyhow::Result<&mut Self>
    where
        T: HasPublic,
    {
        let public_key_hash = get_sha256(&public_key.public_key_to_der()?);
        let tee_report = Report::new(&public_key_hash);
        let attestation_info = AttestationInfo {
            report: tee_report,
            certificate: tee_certificate,
        };
        let tee_extension = attestation_info.to_extension()?;
        self.builder.append_extension(tee_extension)?;
        Ok(self)
    }

    fn add_extensions(
        &mut self,
        extensions: Stack<openssl::x509::X509Extension>,
    ) -> anyhow::Result<&mut Self> {
        for extension in extensions.iter() {
            self.builder.append_extension2(extension)?;
        }
        Ok(self)
    }

    fn build(mut self, private_key: &PKey<Private>) -> anyhow::Result<X509> {
        self.builder.sign(private_key, MessageDigest::sha256())?;
        Ok(self.builder.build())
    }
}
