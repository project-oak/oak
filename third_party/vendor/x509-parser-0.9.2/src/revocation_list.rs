use crate::error::{X509Error, X509Result};
use crate::extensions::*;
use crate::time::ASN1Time;
use crate::x509::{
    parse_serial, parse_signature_value, AlgorithmIdentifier, ReasonCode, X509Name, X509Version,
};

use der_parser::ber::{BerTag, BitStringObject};
use der_parser::der::*;
use der_parser::num_bigint::BigUint;
use der_parser::oid::Oid;
use nom::combinator::{all_consuming, complete, map, opt};
use nom::multi::many1;
use nom::Offset;
use oid_registry::*;
use std::collections::HashMap;

/// An X.509 v2 Certificate Revocation List (CRL).
///
/// X.509 v2 CRLs are defined in [RFC5280](https://tools.ietf.org/html/rfc5280).
#[derive(Debug)]
pub struct CertificateRevocationList<'a> {
    pub tbs_cert_list: TbsCertList<'a>,
    pub signature_algorithm: AlgorithmIdentifier<'a>,
    pub signature_value: BitStringObject<'a>,
}

impl<'a> CertificateRevocationList<'a> {
    /// Parse a DER-encoded X.509 v2 CRL, and return the remaining of the input and the built
    /// object.
    ///
    /// The returned object uses zero-copy, and so has the same lifetime as the input.
    ///
    /// <pre>
    /// CertificateList  ::=  SEQUENCE  {
    ///      tbsCertList          TBSCertList,
    ///      signatureAlgorithm   AlgorithmIdentifier,
    ///      signatureValue       BIT STRING  }
    /// </pre>
    ///
    /// # Example
    ///
    /// To parse a CRL and print information about revoked certificates:
    ///
    /// ```rust
    /// # use x509_parser::parse_x509_crl;
    /// #
    /// # static DER: &'static [u8] = include_bytes!("../assets/example.crl");
    /// #
    /// # fn main() {
    /// let res = parse_x509_crl(DER);
    /// match res {
    ///     Ok((_rem, crl)) => {
    ///         for revoked in crl.iter_revoked_certificates() {
    ///             println!("Revoked certificate serial: {}", revoked.raw_serial_as_string());
    ///             println!("  Reason: {}", revoked.reason_code().unwrap_or_default().1);
    ///         }
    ///     },
    ///     _ => panic!("CRL parsing failed: {:?}", res),
    /// }
    /// # }
    /// ```
    pub fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, tbs_cert_list) = TbsCertList::from_der(i)?;
            let (i, signature_algorithm) = AlgorithmIdentifier::from_der(i)?;
            let (i, signature_value) = parse_signature_value(i)?;
            let crl = CertificateRevocationList {
                tbs_cert_list,
                signature_algorithm,
                signature_value,
            };
            Ok((i, crl))
        })(i)
    }

    /// Get the version of the encoded certificate
    pub fn version(&self) -> Option<X509Version> {
        self.tbs_cert_list.version
    }

    /// Get the certificate issuer.
    #[inline]
    pub fn issuer(&self) -> &X509Name {
        &self.tbs_cert_list.issuer
    }

    /// Get the date and time of the last (this) update.
    #[inline]
    pub fn last_update(&self) -> ASN1Time {
        self.tbs_cert_list.this_update
    }

    /// Get the date and time of the next update, if present.
    #[inline]
    pub fn next_update(&self) -> Option<ASN1Time> {
        self.tbs_cert_list.next_update
    }

    /// Return an iterator over the `RevokedCertificate` objects
    pub fn iter_revoked_certificates(&self) -> impl Iterator<Item = &RevokedCertificate<'a>> {
        self.tbs_cert_list.revoked_certificates.iter()
    }

    /// Get the certificate extensions.
    #[inline]
    pub fn extensions(&self) -> &HashMap<Oid, X509Extension> {
        &self.tbs_cert_list.extensions
    }

    /// Get the CRL number, if present
    ///
    /// Note that the returned value is a `BigUint`, because of the following RFC specification:
    /// <pre>
    /// Given the requirements above, CRL numbers can be expected to contain long integers.  CRL
    /// verifiers MUST be able to handle CRLNumber values up to 20 octets.  Conformant CRL issuers
    /// MUST NOT use CRLNumber values longer than 20 octets.
    /// </pre>
    pub fn crl_number(&self) -> Option<&BigUint> {
        let ext = self.extensions().get(&OID_X509_EXT_CRL_NUMBER)?;
        match ext.parsed_extension {
            ParsedExtension::CRLNumber(ref num) => Some(num),
            _ => None,
        }
    }
}

/// The sequence TBSCertList contains information about the certificates that have
/// been revoked by the CA that issued the CRL.
///
/// RFC5280 definition:
///
/// <pre>
/// TBSCertList  ::=  SEQUENCE  {
///         version                 Version OPTIONAL,
///                                      -- if present, MUST be v2
///         signature               AlgorithmIdentifier,
///         issuer                  Name,
///         thisUpdate              Time,
///         nextUpdate              Time OPTIONAL,
///         revokedCertificates     SEQUENCE OF SEQUENCE  {
///             userCertificate         CertificateSerialNumber,
///             revocationDate          Time,
///             crlEntryExtensions      Extensions OPTIONAL
///                                      -- if present, version MUST be v2
///                                   } OPTIONAL,
///         crlExtensions           [0]  EXPLICIT Extensions OPTIONAL
///                                      -- if present, version MUST be v2
///                             }
/// </pre>
#[derive(Debug, PartialEq)]
pub struct TbsCertList<'a> {
    pub version: Option<X509Version>,
    pub signature: AlgorithmIdentifier<'a>,
    pub issuer: X509Name<'a>,
    pub this_update: ASN1Time,
    pub next_update: Option<ASN1Time>,
    pub revoked_certificates: Vec<RevokedCertificate<'a>>,
    pub extensions: HashMap<Oid<'a>, X509Extension<'a>>,
    pub(crate) raw: &'a [u8],
}

impl<'a> TbsCertList<'a> {
    fn from_der(i: &'a [u8]) -> X509Result<Self> {
        let start_i = i;
        parse_der_sequence_defined_g(move |i, _| {
            let (i, version) =
                opt(map(parse_der_u32, X509Version))(i).or(Err(X509Error::InvalidVersion))?;
            let (i, signature) = AlgorithmIdentifier::from_der(i)?;
            let (i, issuer) = X509Name::from_der(i)?;
            let (i, this_update) = ASN1Time::from_der(i)?;
            let (i, next_update) = ASN1Time::from_der_opt(i)?;
            let (i, revoked_certificates) = opt(complete(parse_revoked_certificates))(i)?;
            let (i, extensions) = parse_extensions(i, BerTag(0))?;
            let len = start_i.offset(i);
            let tbs = TbsCertList {
                version,
                signature,
                issuer,
                this_update,
                next_update,
                revoked_certificates: revoked_certificates.unwrap_or_default(),
                extensions,
                raw: &start_i[..len],
            };
            Ok((i, tbs))
        })(i)
    }
}

impl<'a> AsRef<[u8]> for TbsCertList<'a> {
    fn as_ref(&self) -> &[u8] {
        &self.raw
    }
}

#[derive(Debug, PartialEq)]
pub struct RevokedCertificate<'a> {
    /// The Serial number of the revoked certificate
    pub user_certificate: BigUint,
    /// The date on which the revocation occurred is specified.
    pub revocation_date: ASN1Time,
    /// Additional information about revocation
    pub extensions: HashMap<Oid<'a>, X509Extension<'a>>,
    pub(crate) raw_serial: &'a [u8],
}

impl<'a> RevokedCertificate<'a> {
    // revokedCertificates     SEQUENCE OF SEQUENCE  {
    //     userCertificate         CertificateSerialNumber,
    //     revocationDate          Time,
    //     crlEntryExtensions      Extensions OPTIONAL
    //                                   -- if present, MUST be v2
    //                          }  OPTIONAL,
    pub(crate) fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, (raw_serial, user_certificate)) = parse_serial(i)?;
            let (i, revocation_date) = ASN1Time::from_der(i)?;
            let (i, extensions) = opt(complete(|i| {
                let (rem, v) = parse_extension_sequence(i)?;
                extensions_sequence_to_map(rem, v)
            }))(i)?;
            let revoked = RevokedCertificate {
                user_certificate,
                revocation_date,
                extensions: extensions.unwrap_or_default(),
                raw_serial,
            };
            Ok((i, revoked))
        })(i)
    }

    /// Return the serial number of the revoked certificate
    pub fn serial(&self) -> &BigUint {
        &self.user_certificate
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

    /// Get the code identifying the reason for the revocation, if present
    pub fn reason_code(&self) -> Option<(bool, ReasonCode)> {
        let ext = self.extensions.get(&OID_X509_EXT_REASON_CODE)?;
        match ext.parsed_extension {
            ParsedExtension::ReasonCode(code) => Some((ext.critical, code)),
            _ => None,
        }
    }

    /// Get the invalidity date, if present
    ///
    /// The invalidity date is the date on which it is known or suspected that the private
    ///  key was compromised or that the certificate otherwise became invalid.
    pub fn invalidity_date(&self) -> Option<(bool, ASN1Time)> {
        let ext = self.extensions.get(&OID_X509_EXT_INVALIDITY_DATE)?;
        match ext.parsed_extension {
            ParsedExtension::InvalidityDate(date) => Some((ext.critical, date)),
            _ => None,
        }
    }

    /// Get the certificate extensions.
    #[inline]
    pub fn extensions(&self) -> &HashMap<Oid, X509Extension> {
        &self.extensions
    }
}

fn parse_revoked_certificates(i: &[u8]) -> X509Result<Vec<RevokedCertificate>> {
    parse_der_sequence_defined_g(|a, _| {
        all_consuming(many1(complete(RevokedCertificate::from_der)))(a)
    })(i)
}
