//! X.509 Certificate object definitions and operations

use crate::error::{X509Error, X509Result};
use crate::extensions::*;
use crate::time::ASN1Time;
use crate::x509::{
    parse_serial, parse_signature_value, AlgorithmIdentifier, SubjectPublicKeyInfo, X509Name,
    X509Version,
};

use der_parser::ber::{parse_ber_optional, BerTag, BitStringObject};
use der_parser::der::*;
use der_parser::error::*;
use der_parser::num_bigint::BigUint;
use der_parser::oid::Oid;
use der_parser::*;
use nom::Offset;
use oid_registry::*;
use std::collections::HashMap;

/// An X.509 v3 Certificate.
///
/// X.509 v3 certificates are defined in [RFC5280](https://tools.ietf.org/html/rfc5280), section
/// 4.1. This object uses the same structure for content, so for ex the subject can be accessed
/// using the path `x509.tbs_certificate.subject`.
///
/// `X509Certificate` also contains convenience methods to access the most common fields (subject,
/// issuer, etc.).
///
/// A `X509Certificate` is a zero-copy view over a buffer, so the lifetime is the same as the
/// buffer containing the binary representation.
///
/// ```rust
/// # use x509_parser::parse_x509_certificate;
/// # use x509_parser::certificate::X509Certificate;
/// #
/// # static DER: &'static [u8] = include_bytes!("../assets/IGC_A.der");
/// #
/// fn display_x509_info(x509: &X509Certificate<'_>) {
///      let subject = &x509.tbs_certificate.subject;
///      let issuer = &x509.tbs_certificate.issuer;
///      println!("X.509 Subject: {}", subject);
///      println!("X.509 Issuer: {}", issuer);
///      println!("X.509 serial: {}", x509.tbs_certificate.raw_serial_as_string());
/// }
/// #
/// # fn main() {
/// # let res = parse_x509_certificate(DER);
/// # match res {
/// #     Ok((_rem, x509)) => {
/// #         display_x509_info(&x509);
/// #     },
/// #     _ => panic!("x509 parsing failed: {:?}", res),
/// # }
/// # }
/// ```
#[derive(Debug, PartialEq)]
pub struct X509Certificate<'a> {
    pub tbs_certificate: TbsCertificate<'a>,
    pub signature_algorithm: AlgorithmIdentifier<'a>,
    pub signature_value: BitStringObject<'a>,
}

impl<'a> X509Certificate<'a> {
    /// Parse a DER-encoded X.509 Certificate, and return the remaining of the input and the built
    /// object.
    ///
    /// The returned object uses zero-copy, and so has the same lifetime as the input.
    ///
    /// Note that only parsing is done, not validation.
    ///
    /// <pre>
    /// Certificate  ::=  SEQUENCE  {
    ///         tbsCertificate       TBSCertificate,
    ///         signatureAlgorithm   AlgorithmIdentifier,
    ///         signatureValue       BIT STRING  }
    /// </pre>
    ///
    /// # Example
    ///
    /// To parse a certificate and print the subject and issuer:
    ///
    /// ```rust
    /// # use x509_parser::parse_x509_certificate;
    /// #
    /// # static DER: &'static [u8] = include_bytes!("../assets/IGC_A.der");
    /// #
    /// # fn main() {
    /// let res = parse_x509_certificate(DER);
    /// match res {
    ///     Ok((_rem, x509)) => {
    ///         let subject = &x509.tbs_certificate.subject;
    ///         let issuer = &x509.tbs_certificate.issuer;
    ///         println!("X.509 Subject: {}", subject);
    ///         println!("X.509 Issuer: {}", issuer);
    ///     },
    ///     _ => panic!("x509 parsing failed: {:?}", res),
    /// }
    /// # }
    /// ```
    pub fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, tbs_certificate) = TbsCertificate::from_der(i)?;
            let (i, signature_algorithm) = AlgorithmIdentifier::from_der(i)?;
            let (i, signature_value) = parse_signature_value(i)?;
            let cert = X509Certificate {
                tbs_certificate,
                signature_algorithm,
                signature_value,
            };
            Ok((i, cert))
        })(i)
    }

    /// Get the version of the encoded certificate
    pub fn version(&self) -> X509Version {
        self.tbs_certificate.version
    }

    /// Get the certificate subject.
    #[inline]
    pub fn subject(&self) -> &X509Name {
        &self.tbs_certificate.subject
    }

    /// Get the certificate issuer.
    #[inline]
    pub fn issuer(&self) -> &X509Name {
        &self.tbs_certificate.issuer
    }

    /// Get the certificate validity.
    #[inline]
    pub fn validity(&self) -> &Validity {
        &self.tbs_certificate.validity
    }

    /// Get the certificate extensions.
    #[inline]
    pub fn extensions(&self) -> &HashMap<Oid, X509Extension> {
        self.tbs_certificate.extensions()
    }

    /// Verify the cryptographic signature of this certificate
    ///
    /// `public_key` is the public key of the **signer**. For a self-signed certificate,
    /// (for ex. a public root certificate authority), this is the key from the certificate,
    /// so you can use `None`.
    ///
    /// For a leaf certificate, this is the public key of the certificate that signed it.
    /// It is usually an intermediate authority.
    #[cfg(feature = "verify")]
    pub fn verify_signature(
        &self,
        public_key: Option<&SubjectPublicKeyInfo>,
    ) -> Result<(), X509Error> {
        use ring::signature;
        let spki = public_key.unwrap_or(&self.tbs_certificate.subject_pki);
        let signature_alg = &self.signature_algorithm.algorithm;
        // identify verification algorithm
        let verification_alg: &dyn signature::VerificationAlgorithm =
            if *signature_alg == OID_PKCS1_SHA1WITHRSA {
                &signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY
            } else if *signature_alg == OID_PKCS1_SHA256WITHRSA {
                &signature::RSA_PKCS1_2048_8192_SHA256
            } else if *signature_alg == OID_PKCS1_SHA384WITHRSA {
                &signature::RSA_PKCS1_2048_8192_SHA384
            } else if *signature_alg == OID_PKCS1_SHA512WITHRSA {
                &signature::RSA_PKCS1_2048_8192_SHA512
            } else if *signature_alg == OID_SIG_ECDSA_WITH_SHA256 {
                &signature::ECDSA_P256_SHA256_ASN1
            } else if *signature_alg == OID_SIG_ECDSA_WITH_SHA384 {
                &signature::ECDSA_P384_SHA384_ASN1
            } else {
                return Err(X509Error::SignatureUnsupportedAlgorithm);
            };
        // get public key
        let key = signature::UnparsedPublicKey::new(verification_alg, spki.subject_public_key.data);
        // verify signature
        let sig = self.signature_value.data;
        key.verify(self.tbs_certificate.raw, sig)
            .or(Err(X509Error::SignatureVerificationError))
    }
}

/// The sequence TBSCertificate contains information associated with the
/// subject of the certificate and the CA that issued it.
///
/// RFC5280 definition:
///
/// <pre>
///   TBSCertificate  ::=  SEQUENCE  {
///        version         [0]  EXPLICIT Version DEFAULT v1,
///        serialNumber         CertificateSerialNumber,
///        signature            AlgorithmIdentifier,
///        issuer               Name,
///        validity             Validity,
///        subject              Name,
///        subjectPublicKeyInfo SubjectPublicKeyInfo,
///        issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
///                             -- If present, version MUST be v2 or v3
///        subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
///                             -- If present, version MUST be v2 or v3
///        extensions      [3]  EXPLICIT Extensions OPTIONAL
///                             -- If present, version MUST be v3
///        }
/// </pre>
#[derive(Debug, PartialEq)]
pub struct TbsCertificate<'a> {
    pub version: X509Version,
    pub serial: BigUint,
    pub signature: AlgorithmIdentifier<'a>,
    pub issuer: X509Name<'a>,
    pub validity: Validity,
    pub subject: X509Name<'a>,
    pub subject_pki: SubjectPublicKeyInfo<'a>,
    pub issuer_uid: Option<UniqueIdentifier<'a>>,
    pub subject_uid: Option<UniqueIdentifier<'a>>,
    pub extensions: HashMap<Oid<'a>, X509Extension<'a>>,
    pub(crate) raw: &'a [u8],
    pub(crate) raw_serial: &'a [u8],
}

impl<'a> TbsCertificate<'a> {
    /// Parse a DER-encoded TbsCertificate object
    ///
    /// <pre>
    /// TBSCertificate  ::=  SEQUENCE  {
    ///      version         [0]  Version DEFAULT v1,
    ///      serialNumber         CertificateSerialNumber,
    ///      signature            AlgorithmIdentifier,
    ///      issuer               Name,
    ///      validity             Validity,
    ///      subject              Name,
    ///      subjectPublicKeyInfo SubjectPublicKeyInfo,
    ///      issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
    ///                           -- If present, version MUST be v2 or v3
    ///      subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
    ///                           -- If present, version MUST be v2 or v3
    ///      extensions      [3]  Extensions OPTIONAL
    ///                           -- If present, version MUST be v3 --  }
    /// </pre>
    pub fn from_der(i: &'a [u8]) -> X509Result<TbsCertificate<'a>> {
        let start_i = i;
        parse_der_sequence_defined_g(move |i, _| {
            let (i, version) = X509Version::from_der(i)?;
            let (i, serial) = parse_serial(i)?;
            let (i, signature) = AlgorithmIdentifier::from_der(i)?;
            let (i, issuer) = X509Name::from_der(i)?;
            let (i, validity) = Validity::from_der(i)?;
            let (i, subject) = X509Name::from_der(i)?;
            let (i, subject_pki) = SubjectPublicKeyInfo::from_der(i)?;
            let (i, issuer_uid) = UniqueIdentifier::from_der_issuer(i)?;
            let (i, subject_uid) = UniqueIdentifier::from_der_subject(i)?;
            let (i, extensions) = parse_extensions(i, BerTag(3))?;
            let len = start_i.offset(i);
            let tbs = TbsCertificate {
                version,
                serial: serial.1,
                signature,
                issuer,
                validity,
                subject,
                subject_pki,
                issuer_uid,
                subject_uid,
                extensions,

                raw: &start_i[..len],
                raw_serial: serial.0,
            };
            Ok((i, tbs))
        })(i)
    }

    /// Get a reference to the map of extensions.
    pub fn extensions(&self) -> &HashMap<Oid, X509Extension> {
        &self.extensions
    }

    pub fn basic_constraints(&self) -> Option<(bool, &BasicConstraints)> {
        let ext = self.extensions.get(&OID_X509_EXT_BASIC_CONSTRAINTS)?;
        match ext.parsed_extension {
            ParsedExtension::BasicConstraints(ref bc) => Some((ext.critical, bc)),
            _ => None,
        }
    }

    pub fn key_usage(&self) -> Option<(bool, &KeyUsage)> {
        let ext = self.extensions.get(&OID_X509_EXT_KEY_USAGE)?;
        match ext.parsed_extension {
            ParsedExtension::KeyUsage(ref ku) => Some((ext.critical, ku)),
            _ => None,
        }
    }

    pub fn extended_key_usage(&self) -> Option<(bool, &ExtendedKeyUsage)> {
        let ext = self.extensions.get(&OID_X509_EXT_EXTENDED_KEY_USAGE)?;
        match ext.parsed_extension {
            ParsedExtension::ExtendedKeyUsage(ref eku) => Some((ext.critical, eku)),
            _ => None,
        }
    }

    pub fn policy_constraints(&self) -> Option<(bool, &PolicyConstraints)> {
        let ext = self.extensions.get(&OID_X509_EXT_POLICY_CONSTRAINTS)?;
        match ext.parsed_extension {
            ParsedExtension::PolicyConstraints(ref pc) => Some((ext.critical, pc)),
            _ => None,
        }
    }

    pub fn inhibit_anypolicy(&self) -> Option<(bool, &InhibitAnyPolicy)> {
        let ext = self.extensions.get(&OID_X509_EXT_INHIBITANT_ANY_POLICY)?;
        match ext.parsed_extension {
            ParsedExtension::InhibitAnyPolicy(ref iap) => Some((ext.critical, iap)),
            _ => None,
        }
    }

    pub fn policy_mappings(&self) -> Option<(bool, &PolicyMappings)> {
        let ext = self.extensions.get(&OID_X509_EXT_POLICY_MAPPINGS)?;
        match ext.parsed_extension {
            ParsedExtension::PolicyMappings(ref pm) => Some((ext.critical, pm)),
            _ => None,
        }
    }

    pub fn subject_alternative_name(&self) -> Option<(bool, &SubjectAlternativeName)> {
        let ext = self.extensions.get(&OID_X509_EXT_SUBJECT_ALT_NAME)?;
        match ext.parsed_extension {
            ParsedExtension::SubjectAlternativeName(ref san) => Some((ext.critical, san)),
            _ => None,
        }
    }

    pub fn name_constraints(&self) -> Option<(bool, &NameConstraints)> {
        let ext = self.extensions.get(&OID_X509_EXT_NAME_CONSTRAINTS)?;
        match ext.parsed_extension {
            ParsedExtension::NameConstraints(ref nc) => Some((ext.critical, nc)),
            _ => None,
        }
    }

    /// Returns true if certificate has `basicConstraints CA:true`
    pub fn is_ca(&self) -> bool {
        self.basic_constraints()
            .map(|(_, bc)| bc.ca)
            .unwrap_or(false)
    }

    /// Get the raw bytes of the certificate serial number
    pub fn raw_serial(&self) -> &[u8] {
        self.raw_serial
    }

    /// Get a formatted string of the certificate serial number, separated by ':'
    pub fn raw_serial_as_string(&self) -> String {
        let mut s = self
            .raw_serial
            .iter()
            .fold(String::with_capacity(3 * self.raw_serial.len()), |a, b| {
                a + &format!("{:02x}:", b)
            });
        s.pop();
        s
    }
}

impl<'a> AsRef<[u8]> for TbsCertificate<'a> {
    fn as_ref(&self) -> &[u8] {
        &self.raw
    }
}

#[derive(Debug, PartialEq)]
pub struct Validity {
    pub not_before: ASN1Time,
    pub not_after: ASN1Time,
}

impl Validity {
    fn from_der(i: &[u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, not_before) = ASN1Time::from_der(i)?;
            let (i, not_after) = ASN1Time::from_der(i)?;
            let v = Validity {
                not_before,
                not_after,
            };
            Ok((i, v))
        })(i)
    }

    /// The time left before the certificate expires.
    ///
    /// If the certificate is not currently valid, then `None` is
    /// returned.  Otherwise, the `Duration` until the certificate
    /// expires is returned.
    pub fn time_to_expiration(&self) -> Option<std::time::Duration> {
        let now = ASN1Time::now();
        if !self.is_valid_at(now) {
            return None;
        }
        // Note that the duration below is guaranteed to be positive,
        // since we just checked that now < na
        self.not_after - now
    }

    /// Check the certificate time validity for the provided date/time
    #[inline]
    pub fn is_valid_at(&self, time: ASN1Time) -> bool {
        time >= self.not_before && time < self.not_after
    }

    /// Check the certificate time validity
    #[inline]
    pub fn is_valid(&self) -> bool {
        self.is_valid_at(ASN1Time::now())
    }
}

#[derive(Debug, PartialEq)]
pub struct UniqueIdentifier<'a>(pub BitStringObject<'a>);

impl<'a> UniqueIdentifier<'a> {
    // issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL
    fn from_der_issuer(i: &'a [u8]) -> X509Result<Option<Self>> {
        Self::parse(i, 1).map_err(|_| X509Error::InvalidIssuerUID.into())
    }

    // subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL
    fn from_der_subject(i: &[u8]) -> X509Result<Option<UniqueIdentifier>> {
        Self::parse(i, 2).map_err(|_| X509Error::InvalidSubjectUID.into())
    }

    // Parse a [tag] UniqueIdentifier OPTIONAL
    //
    // UniqueIdentifier  ::=  BIT STRING
    fn parse(i: &[u8], tag: u32) -> BerResult<Option<UniqueIdentifier>> {
        let (rem, obj) = parse_ber_optional(parse_der_tagged_implicit(
            tag,
            parse_der_content(DerTag::BitString),
        ))(i)?;
        let unique_id = match obj.content {
            DerObjectContent::Optional(None) => Ok(None),
            DerObjectContent::Optional(Some(o)) => match o.content {
                DerObjectContent::BitString(_, b) => Ok(Some(UniqueIdentifier(b.to_owned()))),
                _ => Err(BerError::BerTypeError),
            },
            _ => Err(BerError::BerTypeError),
        }?;
        Ok((rem, unique_id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_validity_expiration() {
        let mut v = Validity {
            not_before: ASN1Time::now(),
            not_after: ASN1Time::now(),
        };
        assert_eq!(v.time_to_expiration(), None);
        v.not_after = (v.not_after + std::time::Duration::new(60, 0)).unwrap();
        assert!(v.time_to_expiration().is_some());
        assert!(v.time_to_expiration().unwrap() <= std::time::Duration::from_secs(60));
        // The following assumes this timing won't take 10 seconds... I
        // think that is safe.
        assert!(v.time_to_expiration().unwrap() > std::time::Duration::from_secs(50));
    }
}
