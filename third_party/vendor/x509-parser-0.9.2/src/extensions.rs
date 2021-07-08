//! X.509 Extensions objects and types

use crate::error::{X509Error, X509Result};
use crate::time::{der_to_utctime, ASN1Time};
use crate::x509::{ReasonCode, X509Name};

use der_parser::der::*;
use der_parser::error::BerResult;
use der_parser::num_bigint::BigUint;
use der_parser::oid::Oid;
use nom::combinator::{all_consuming, complete, map_opt, map_res, opt};
use nom::multi::{many0, many1};
use nom::{exact, Err};
use oid_registry::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, PartialEq)]
pub struct X509Extension<'a> {
    /// OID describing the extension content
    pub oid: Oid<'a>,
    /// Boolean value describing the 'critical' attribute of the extension
    ///
    /// An extension includes the boolean critical, with a default value of FALSE.
    pub critical: bool,
    /// Raw content of the extension
    pub value: &'a [u8],
    pub(crate) parsed_extension: ParsedExtension<'a>,
}

impl<'a> X509Extension<'a> {
    /// Parse a DER-encoded X.509 extension
    ///
    /// X.509 extensions allow adding attributes to objects like certificates or revocation lists.
    ///
    /// Each extension in a certificate is designated as either critical or non-critical.  A
    /// certificate using system MUST reject the certificate if it encounters a critical extension it
    /// does not recognize; however, a non-critical extension MAY be ignored if it is not recognized.
    ///
    /// Each extension includes an OID and an ASN.1 structure.  When an extension appears in a
    /// certificate, the OID appears as the field extnID and the corresponding ASN.1 encoded structure
    /// is the value of the octet string extnValue.  A certificate MUST NOT include more than one
    /// instance of a particular extension.
    ///
    /// This function parses the global structure (described above), and will return the object if it
    /// succeeds. During this step, it also attempts to parse the content of the extension, if known.
    /// The returned object has a
    /// [parsed_extension](x509/struct.X509Extension.html#method.parsed_extension) method. The returned
    /// enum is either a known extension, or the special value `ParsedExtension::UnsupportedExtension`.
    ///
    /// <pre>
    /// Extension  ::=  SEQUENCE  {
    ///     extnID      OBJECT IDENTIFIER,
    ///     critical    BOOLEAN DEFAULT FALSE,
    ///     extnValue   OCTET STRING  }
    /// </pre>
    ///
    /// # Example
    ///
    /// ```rust
    /// # use x509_parser::extensions::{X509Extension, ParsedExtension};
    /// #
    /// static DER: &[u8] = &[
    ///    0x30, 0x1D, 0x06, 0x03, 0x55, 0x1D, 0x0E, 0x04, 0x16, 0x04, 0x14, 0xA3, 0x05, 0x2F, 0x18,
    ///    0x60, 0x50, 0xC2, 0x89, 0x0A, 0xDD, 0x2B, 0x21, 0x4F, 0xFF, 0x8E, 0x4E, 0xA8, 0x30, 0x31,
    ///    0x36 ];
    ///
    /// # fn main() {
    /// let res = X509Extension::from_der(DER);
    /// match res {
    ///     Ok((_rem, ext)) => {
    ///         println!("Extension OID: {}", ext.oid);
    ///         println!("  Critical: {}", ext.critical);
    ///         let parsed_ext = ext.parsed_extension();
    ///         assert!(*parsed_ext != ParsedExtension::UnsupportedExtension);
    ///         if let ParsedExtension::SubjectKeyIdentifier(key_id) = parsed_ext {
    ///             assert!(key_id.0.len() > 0);
    ///         } else {
    ///             panic!("Extension has wrong type");
    ///         }
    ///     },
    ///     _ => panic!("x509 extension parsing failed: {:?}", res),
    /// }
    /// # }
    /// ```
    pub fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, oid) = map_res(parse_der_oid, |x| x.as_oid_val())(i)?;
            let (i, critical) = der_read_critical(i)?;
            let (i, value) = map_res(parse_der_octetstring, |x| x.as_slice())(i)?;
            let (i, parsed_extension) = crate::extensions::parser::parse_extension(i, value, &oid)?;
            let ext = X509Extension {
                oid,
                critical,
                value,
                parsed_extension,
            };
            Ok((i, ext))
        })(i)
        .map_err(|_| X509Error::InvalidExtensions.into())
    }

    pub fn new(
        oid: Oid<'a>,
        critical: bool,
        value: &'a [u8],
        parsed_extension: ParsedExtension<'a>,
    ) -> X509Extension<'a> {
        X509Extension {
            oid,
            critical,
            value,
            parsed_extension,
        }
    }

    /// Return the extension type or `UnsupportedExtension` if the extension is not implemented.
    pub fn parsed_extension(&self) -> &ParsedExtension<'a> {
        &self.parsed_extension
    }
}

#[derive(Debug, PartialEq)]
pub enum ParsedExtension<'a> {
    /// Crate parser does not support this extension (yet)
    UnsupportedExtension,
    ParseError,
    /// Section 4.2.1.1 of rfc 5280
    AuthorityKeyIdentifier(AuthorityKeyIdentifier<'a>),
    /// Section 4.2.1.2 of rfc 5280
    SubjectKeyIdentifier(KeyIdentifier<'a>),
    /// Section 4.2.1.3 of rfc 5280
    KeyUsage(KeyUsage),
    /// Section 4.2.1.4 of rfc 5280
    CertificatePolicies(CertificatePolicies<'a>),
    /// Section 4.2.1.5 of rfc 5280
    PolicyMappings(PolicyMappings<'a>),
    /// Section 4.2.1.6 of rfc 5280
    SubjectAlternativeName(SubjectAlternativeName<'a>),
    /// Section 4.2.1.9 of rfc 5280
    BasicConstraints(BasicConstraints),
    /// Section 4.2.1.10 of rfc 5280
    NameConstraints(NameConstraints<'a>),
    /// Section 4.2.1.11 of rfc 5280
    PolicyConstraints(PolicyConstraints),
    /// Section 4.2.1.12 of rfc 5280
    ExtendedKeyUsage(ExtendedKeyUsage<'a>),
    /// Section 4.2.1.14 of rfc 5280
    InhibitAnyPolicy(InhibitAnyPolicy),
    /// Section 4.2.2.1 of rfc 5280
    AuthorityInfoAccess(AuthorityInfoAccess<'a>),
    /// Netscape certificate type (subject is SSL client, an SSL server, or a CA)
    NSCertType(NSCertType),
    /// Section 5.3.1 of rfc 5280
    CRLNumber(BigUint),
    /// Section 5.3.1 of rfc 5280
    ReasonCode(ReasonCode),
    /// Section 5.3.3 of rfc 5280
    InvalidityDate(ASN1Time),
}

#[derive(Debug, PartialEq)]
pub struct AuthorityKeyIdentifier<'a> {
    pub key_identifier: Option<KeyIdentifier<'a>>,
    pub authority_cert_issuer: Option<Vec<GeneralName<'a>>>,
    pub authority_cert_serial: Option<&'a [u8]>,
}

#[derive(Debug, PartialEq)]
pub struct CertificatePolicies<'a> {
    pub policies: HashMap<Oid<'a>, &'a [u8]>,
}

/// Identifies whether the subject of the certificate is a CA, and the max validation depth.
#[derive(Debug, PartialEq)]
pub struct BasicConstraints {
    pub ca: bool,
    pub path_len_constraint: Option<u32>,
}

#[derive(Debug, PartialEq)]
pub struct KeyIdentifier<'a>(pub &'a [u8]);

#[derive(Debug, PartialEq)]
pub struct KeyUsage {
    pub flags: u16,
}

impl KeyUsage {
    pub fn digital_signature(&self) -> bool {
        self.flags & 1 == 1
    }
    pub fn non_repudiation(&self) -> bool {
        (self.flags >> 1) & 1u16 == 1
    }
    pub fn key_encipherment(&self) -> bool {
        (self.flags >> 2) & 1u16 == 1
    }
    pub fn data_encipherment(&self) -> bool {
        (self.flags >> 3) & 1u16 == 1
    }
    pub fn key_agreement(&self) -> bool {
        (self.flags >> 4) & 1u16 == 1
    }
    pub fn key_cert_sign(&self) -> bool {
        (self.flags >> 5) & 1u16 == 1
    }
    pub fn crl_sign(&self) -> bool {
        (self.flags >> 6) & 1u16 == 1
    }
    pub fn encipher_only(&self) -> bool {
        (self.flags >> 7) & 1u16 == 1
    }
    pub fn decipher_only(&self) -> bool {
        (self.flags >> 8) & 1u16 == 1
    }
}

// This list must have the same order as KeyUsage flags declaration (4.2.1.3)
const KEY_USAGE_FLAGS: &[&str] = &[
    "Digital Signature",
    "Non Repudiation",
    "Key Encipherment",
    "Data Encipherment",
    "Key Agreement",
    "Key Cert Sign",
    "CRL Sign",
    "Encipher Only",
    "Decipher Only",
];

impl fmt::Display for KeyUsage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = KEY_USAGE_FLAGS
            .iter()
            .enumerate()
            .fold(String::new(), |acc, (idx, s)| {
                if self.flags >> idx & 1 != 0 {
                    acc + s + ", "
                } else {
                    acc
                }
            });
        s.pop();
        s.pop();
        f.write_str(&s)
    }
}

#[derive(Debug, PartialEq)]
pub struct ExtendedKeyUsage<'a> {
    pub any: bool,
    pub server_auth: bool,
    pub client_auth: bool,
    pub code_signing: bool,
    pub email_protection: bool,
    pub time_stamping: bool,
    pub ocscp_signing: bool,
    pub other: Vec<Oid<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct NSCertType(u8);

// The value is a bit-string, where the individual bit positions are defined as:
//
//     bit-0 SSL client - this cert is certified for SSL client authentication use
//     bit-1 SSL server - this cert is certified for SSL server authentication use
//     bit-2 S/MIME - this cert is certified for use by clients (New in PR3)
//     bit-3 Object Signing - this cert is certified for signing objects such as Java applets and plugins(New in PR3)
//     bit-4 Reserved - this bit is reserved for future use
//     bit-5 SSL CA - this cert is certified for issuing certs for SSL use
//     bit-6 S/MIME CA - this cert is certified for issuing certs for S/MIME use (New in PR3)
//     bit-7 Object Signing CA - this cert is certified for issuing certs for Object Signing (New in PR3)
impl NSCertType {
    pub fn ssl_client(&self) -> bool {
        self.0 & 0x1 == 1
    }
    pub fn ssl_server(&self) -> bool {
        (self.0 >> 1) & 1 == 1
    }
    pub fn smime(&self) -> bool {
        (self.0 >> 2) & 1 == 1
    }
    pub fn object_signing(&self) -> bool {
        (self.0 >> 3) & 1 == 1
    }
    pub fn ssl_ca(&self) -> bool {
        (self.0 >> 5) & 1 == 1
    }
    pub fn smime_ca(&self) -> bool {
        (self.0 >> 6) & 1 == 1
    }
    pub fn object_signing_ca(&self) -> bool {
        (self.0 >> 7) & 1 == 1
    }
}

const NS_CERT_TYPE_FLAGS: &[&str] = &[
    "SSL CLient",
    "SSL Server",
    "S/MIME",
    "Object Signing",
    "Reserved",
    "SSL CA",
    "S/MIME CA",
    "Object Signing CA",
];

impl fmt::Display for NSCertType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let mut acc = self.0;
        for flag_text in NS_CERT_TYPE_FLAGS {
            if acc & 1 != 0 {
                s = s + flag_text + ", ";
            }
            acc >>= 1;
        }
        s.pop();
        s.pop();
        f.write_str(&s)
    }
}

#[derive(Debug, PartialEq)]
pub struct AuthorityInfoAccess<'a> {
    pub accessdescs: HashMap<Oid<'a>, Vec<GeneralName<'a>>>,
}

#[derive(Debug, PartialEq)]
pub struct InhibitAnyPolicy {
    pub skip_certs: u32,
}

#[derive(Debug, PartialEq)]
pub struct PolicyMappings<'a> {
    pub mappings: HashMap<Oid<'a>, Vec<Oid<'a>>>,
}

#[derive(Debug, PartialEq)]
pub struct PolicyConstraints {
    pub require_explicit_policy: Option<u32>,
    pub inhibit_policy_mapping: Option<u32>,
}

#[derive(Debug, PartialEq)]
pub struct SubjectAlternativeName<'a> {
    pub general_names: Vec<GeneralName<'a>>,
}

#[derive(Debug, PartialEq)]
/// Represents a GeneralName as defined in RFC5280. There
/// is no support X.400 addresses and EDIPartyName.
///
/// String formats are not validated.
pub enum GeneralName<'a> {
    OtherName(Oid<'a>, &'a [u8]),
    /// More or less an e-mail, the format is not checked.
    RFC822Name(&'a str),
    /// A hostname, format is not checked.
    DNSName(&'a str),
    // X400Address,
    /// RFC5280 defines several string types, we always try to parse as utf-8
    /// which is more or less a superset of the string types.
    DirectoryName(X509Name<'a>),
    // EDIPartyName { name_assigner: Option<&'a str>, party_name: &'a str },
    /// An uniform resource identifier. The format is not checked.
    URI(&'a str),
    /// An ip address, provided as encoded.
    IPAddress(&'a [u8]),
    RegisteredID(Oid<'a>),
}

#[derive(Debug, PartialEq)]
pub struct NameConstraints<'a> {
    pub permitted_subtrees: Option<Vec<GeneralSubtree<'a>>>,
    pub excluded_subtrees: Option<Vec<GeneralSubtree<'a>>>,
}

#[derive(Debug, PartialEq)]
/// Represents the structure used in the name constraints extensions.
/// The fields minimum and maximum are not supported (openssl also has no support).
pub struct GeneralSubtree<'a> {
    pub base: GeneralName<'a>,
    // minimum: u32,
    // maximum: Option<u32>,
}

pub(crate) mod parser {
    use crate::extensions::*;
    use der_parser::error::BerError;
    use der_parser::{oid::Oid, *};
    use lazy_static::lazy_static;
    use nom::combinator::{map, verify};
    use nom::{Err, IResult};

    type ExtParser = fn(&[u8]) -> IResult<&[u8], ParsedExtension, BerError>;

    lazy_static! {
        static ref EXTENSION_PARSERS: HashMap<Oid<'static>, ExtParser> = {
            macro_rules! add {
                ($m:ident, $oid:ident, $p:ident) => {
                    $m.insert($oid, $p as ExtParser);
                };
            }

            let mut m = HashMap::new();
            add!(m, OID_X509_EXT_SUBJECT_KEY_IDENTIFIER, parse_keyidentifier);
            add!(m, OID_X509_EXT_KEY_USAGE, parse_keyusage);
            add!(
                m,
                OID_X509_EXT_SUBJECT_ALT_NAME,
                parse_subjectalternativename
            );
            add!(m, OID_X509_EXT_BASIC_CONSTRAINTS, parse_basicconstraints);
            add!(m, OID_X509_EXT_NAME_CONSTRAINTS, parse_nameconstraints);
            add!(
                m,
                OID_X509_EXT_CERTIFICATE_POLICIES,
                parse_certificatepolicies
            );
            add!(m, OID_X509_EXT_POLICY_MAPPINGS, parse_policymappings);
            add!(m, OID_X509_EXT_POLICY_CONSTRAINTS, parse_policyconstraints);
            add!(m, OID_X509_EXT_EXTENDED_KEY_USAGE, parse_extendedkeyusage);
            add!(
                m,
                OID_X509_EXT_INHIBITANT_ANY_POLICY,
                parse_inhibitanypolicy
            );
            add!(m, OID_PKIX_AUTHORITY_INFO_ACCESS, parse_authorityinfoaccess);
            add!(
                m,
                OID_X509_EXT_AUTHORITY_KEY_IDENTIFIER,
                parse_authoritykeyidentifier
            );
            add!(m, OID_X509_EXT_CERT_TYPE, parse_nscerttype);
            add!(m, OID_X509_EXT_CRL_NUMBER, parse_crl_number);
            add!(m, OID_X509_EXT_REASON_CODE, parse_reason_code);
            add!(m, OID_X509_EXT_INVALIDITY_DATE, parse_invalidity_date);
            m
        };
    }

    // look into the parser map if the extension is known, and parse it
    // otherwise, leave it as UnsupportedExtension
    fn parse_extension0<'a>(
        orig_i: &'a [u8],
        i: &'a [u8],
        oid: &Oid,
    ) -> IResult<&'a [u8], ParsedExtension<'a>, BerError> {
        if let Some(parser) = EXTENSION_PARSERS.get(oid) {
            let (_, ext) = parser(i)?;
            Ok((orig_i, ext))
        } else {
            Ok((orig_i, ParsedExtension::UnsupportedExtension))
        }
    }

    pub(crate) fn parse_extension<'a>(
        orig_i: &'a [u8],
        i: &'a [u8],
        oid: &Oid,
    ) -> IResult<&'a [u8], ParsedExtension<'a>, BerError> {
        let r = parse_extension0(orig_i, i, oid);
        if let Err(nom::Err::Incomplete(_)) = r {
            return Ok((orig_i, ParsedExtension::UnsupportedExtension));
        }
        r
    }

    /// Parse a "Basic Constraints" extension
    ///
    /// <pre>
    ///   id-ce-basicConstraints OBJECT IDENTIFIER ::=  { id-ce 19 }
    ///   BasicConstraints ::= SEQUENCE {
    ///        cA                      BOOLEAN DEFAULT FALSE,
    ///        pathLenConstraint       INTEGER (0..MAX) OPTIONAL }
    /// </pre>
    ///
    /// Note the maximum length of the `pathLenConstraint` field is limited to the size of a 32-bits
    /// unsigned integer, and parsing will fail if value if larger.
    fn parse_basicconstraints(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (rem, obj) = parse_der_sequence(i)?;
        if let Ok(seq) = obj.as_sequence() {
            let (ca, path_len_constraint) = match seq.len() {
                0 => (false, None),
                1 => {
                    if let Ok(b) = seq[0].as_bool() {
                        (b, None)
                    } else if let Ok(u) = seq[0].as_u32() {
                        (false, Some(u))
                    } else {
                        return Err(nom::Err::Error(BerError::InvalidTag));
                    }
                }
                2 => {
                    let ca = seq[0]
                        .as_bool()
                        .or(Err(nom::Err::Error(BerError::InvalidLength)))?;
                    let pl = seq[1]
                        .as_u32()
                        .or(Err(nom::Err::Error(BerError::InvalidLength)))?;
                    (ca, Some(pl))
                }
                _ => return Err(nom::Err::Error(BerError::InvalidLength)),
            };
            Ok((
                rem,
                ParsedExtension::BasicConstraints(BasicConstraints {
                    ca,
                    path_len_constraint,
                }),
            ))
        } else {
            Err(nom::Err::Error(BerError::InvalidLength))
        }
    }

    fn parse_nameconstraints<'a>(i: &'a [u8]) -> IResult<&'a [u8], ParsedExtension, BerError> {
        fn parse_subtree<'a>(i: &'a [u8]) -> IResult<&'a [u8], GeneralSubtree, BerError> {
            parse_der_sequence_defined_g(|input, _| {
                map(parse_generalname, |base| GeneralSubtree { base })(input)
            })(i)
        }
        fn parse_subtrees(i: &[u8]) -> IResult<&[u8], Vec<GeneralSubtree>, BerError> {
            all_consuming(many1(complete(parse_subtree)))(i)
        }

        let (ret, named_constraints) = parse_der_sequence_defined_g(|input, _| {
            let (rem, permitted_subtrees) =
                opt(complete(parse_der_tagged_explicit_g(0, |input, _| {
                    parse_subtrees(input)
                })))(input)?;
            let (rem, excluded_subtrees) =
                opt(complete(parse_der_tagged_explicit_g(1, |input, _| {
                    parse_subtrees(input)
                })))(rem)?;
            let named_constraints = NameConstraints {
                permitted_subtrees,
                excluded_subtrees,
            };
            Ok((rem, named_constraints))
        })(i)?;

        Ok((ret, ParsedExtension::NameConstraints(named_constraints)))
    }

    fn parse_generalname<'a>(i: &'a [u8]) -> IResult<&'a [u8], GeneralName, BerError> {
        let (rest, hdr) = verify(der_read_element_header, |hdr| hdr.is_contextspecific())(i)?;
        let len = hdr.len.primitive()?;
        if len > rest.len() {
            return Err(nom::Err::Failure(BerError::ObjectTooShort));
        }
        fn ia5str<'a>(i: &'a [u8], hdr: DerObjectHeader) -> Result<&'a str, Err<BerError>> {
            der_read_element_content_as(i, DerTag::Ia5String, hdr.len, hdr.is_constructed(), 0)?
                .1
                .as_slice()
                .and_then(|s| std::str::from_utf8(s).map_err(|_| BerError::BerValueError))
                .map_err(nom::Err::Failure)
        }
        let name = match hdr.tag.0 {
            0 => {
                // otherName SEQUENCE { OID, [0] explicit any defined by oid }
                let (any, oid) = parse_der_oid(rest)?;
                let oid = oid.as_oid_val().map_err(nom::Err::Failure)?;
                GeneralName::OtherName(oid, any)
            }
            1 => GeneralName::RFC822Name(ia5str(rest, hdr)?),
            2 => GeneralName::DNSName(ia5str(rest, hdr)?),
            3 => return Err(Err::Failure(BerError::Unsupported)), // x400Address
            4 => {
                // directoryName, name
                let (_, name) = all_consuming(X509Name::from_der)(&rest[..len])
                    .or(Err(BerError::Unsupported)) // XXX remove me
                    ?;
                GeneralName::DirectoryName(name)
            }
            5 => return Err(Err::Failure(BerError::Unsupported)), // ediPartyName
            6 => GeneralName::URI(ia5str(rest, hdr)?),
            7 => {
                // IPAddress, OctetString
                let ip = der_read_element_content_as(
                    rest,
                    DerTag::OctetString,
                    hdr.len,
                    hdr.is_constructed(),
                    0,
                )?
                .1
                .as_slice()
                .map_err(nom::Err::Failure)?;
                GeneralName::IPAddress(ip)
            }
            8 => {
                let oid = der_read_element_content_as(
                    rest,
                    DerTag::Oid,
                    hdr.len,
                    hdr.is_constructed(),
                    0,
                )?
                .1
                .as_oid_val()
                .map_err(nom::Err::Failure)?;
                GeneralName::RegisteredID(oid)
            }
            _ => return Err(Err::Failure(BerError::UnknownTag)),
        };
        Ok((&rest[len..], name))
    }

    fn parse_subjectalternativename<'a>(
        i: &'a [u8],
    ) -> IResult<&'a [u8], ParsedExtension, BerError> {
        parse_der_sequence_defined_g(|input, _| {
            let (i, general_names) = all_consuming(many0(complete(parse_generalname)))(input)?;
            Ok((
                i,
                ParsedExtension::SubjectAlternativeName(SubjectAlternativeName { general_names }),
            ))
        })(i)
    }

    fn parse_policyconstraints(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        parse_der_sequence_defined_g(|input, _| {
            let (i, require_explicit_policy) = opt(complete(map_res(
                parse_der_tagged_implicit(0, parse_der_content(DerTag::Integer)),
                |x| x.as_u32(),
            )))(input)?;
            let (i, inhibit_policy_mapping) = all_consuming(opt(complete(map_res(
                parse_der_tagged_implicit(1, parse_der_content(DerTag::Integer)),
                |x| x.as_u32(),
            ))))(i)?;
            let policy_constraint = PolicyConstraints {
                require_explicit_policy,
                inhibit_policy_mapping,
            };
            Ok((i, ParsedExtension::PolicyConstraints(policy_constraint)))
        })(i)
    }

    // PolicyMappings ::= SEQUENCE SIZE (1..MAX) OF SEQUENCE {
    //  issuerDomainPolicy      CertPolicyId,
    //  subjectDomainPolicy     CertPolicyId }
    fn parse_policymappings(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        fn parse_oid_pair(i: &[u8]) -> IResult<&[u8], Vec<DerObject<'_>>, BerError> {
            // read 2 OID as a SEQUENCE OF OID - length will be checked later
            parse_der_sequence_of_v(parse_der_oid)(i)
        }
        let (ret, pairs) = parse_der_sequence_of_v(parse_oid_pair)(i)?;
        let mut mappings: HashMap<Oid, Vec<Oid>> = HashMap::new();
        for pair in pairs.iter() {
            if pair.len() != 2 {
                return Err(Err::Failure(BerError::BerValueError));
            }
            let left = pair[0].as_oid_val().map_err(nom::Err::Failure)?;
            let right = pair[1].as_oid_val().map_err(nom::Err::Failure)?;
            if left.bytes() == oid!(raw 2.5.29.32.0) || right.bytes() == oid!(raw 2.5.29.32.0) {
                // mapping to or from anyPolicy is not allowed
                return Err(Err::Failure(BerError::InvalidTag));
            }
            mappings
                .entry(left)
                .and_modify(|v| v.push(right.clone()))
                .or_insert_with(|| vec![right.clone()]);
        }
        Ok((
            ret,
            ParsedExtension::PolicyMappings(PolicyMappings { mappings }),
        ))
    }

    fn parse_inhibitanypolicy(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (ret, skip_certs) = map_res(parse_der_integer, |x: DerObject| x.as_u32())(i)?;
        Ok((
            ret,
            ParsedExtension::InhibitAnyPolicy(InhibitAnyPolicy { skip_certs }),
        ))
    }

    fn parse_extendedkeyusage(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (ret, seq) = parse_der_sequence_of(parse_der_oid)(i)?;
        let mut seen = std::collections::HashSet::new();
        let mut eku = ExtendedKeyUsage {
            any: false,
            server_auth: false,
            client_auth: false,
            code_signing: false,
            email_protection: false,
            time_stamping: false,
            ocscp_signing: false,
            other: Vec::new(),
        };
        for oid in seq.as_sequence().map_err(nom::Err::Failure)?.iter() {
            let oid = oid.as_oid_val().map_err(nom::Err::Failure)?;
            if !seen.insert(oid.clone()) {
                continue;
            }
            let asn1 = oid.bytes();
            if asn1 == oid!(raw 2.5.29.37.0) {
                eku.any = true;
            } else if asn1 == oid!(raw 1.3.6.1.5.5.7.3.1) {
                eku.server_auth = true;
            } else if asn1 == oid!(raw 1.3.6.1.5.5.7.3.2) {
                eku.client_auth = true;
            } else if asn1 == oid!(raw 1.3.6.1.5.5.7.3.3) {
                eku.code_signing = true;
            } else if asn1 == oid!(raw 1.3.6.1.5.5.7.3.4) {
                eku.email_protection = true;
            } else if asn1 == oid!(raw 1.3.6.1.5.5.7.3.8) {
                eku.time_stamping = true;
            } else if asn1 == oid!(raw 1.3.6.1.5.5.7.3.9) {
                eku.ocscp_signing = true;
            } else {
                eku.other.push(oid);
            }
        }
        Ok((ret, ParsedExtension::ExtendedKeyUsage(eku)))
    }

    // AuthorityInfoAccessSyntax  ::=
    //         SEQUENCE SIZE (1..MAX) OF AccessDescription
    //
    // AccessDescription  ::=  SEQUENCE {
    //         accessMethod          OBJECT IDENTIFIER,
    //         accessLocation        GeneralName  }
    fn parse_authorityinfoaccess(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        fn parse_aia(i: &[u8]) -> IResult<&[u8], (Oid, GeneralName), BerError> {
            parse_der_sequence_defined_g(|content, _| {
                // Read first element, an oid.
                let (gn, oid) = map_res(parse_der_oid, |x: DerObject| x.as_oid_val())(content)?;
                // Parse second element
                let (rest, gn) = parse_generalname(gn)?;
                Ok((rest, (oid, gn)))
            })(i)
        }
        let (ret, mut aia_list) = parse_der_sequence_of_v(parse_aia)(i)?;
        // create the hashmap and merge entries with same OID
        let mut accessdescs: HashMap<Oid, Vec<GeneralName>> = HashMap::new();
        for (oid, gn) in aia_list.drain(..) {
            if let Some(general_names) = accessdescs.get_mut(&oid) {
                general_names.push(gn);
            } else {
                accessdescs.insert(oid, vec![gn]);
            }
        }
        Ok((
            ret,
            ParsedExtension::AuthorityInfoAccess(AuthorityInfoAccess { accessdescs }),
        ))
    }

    fn parse_aki_content<'a>(
        i: &'a [u8],
        _hdr: DerObjectHeader<'_>,
    ) -> IResult<&'a [u8], AuthorityKeyIdentifier<'a>, BerError> {
        let (i, key_identifier) = opt(complete(parse_der_tagged_implicit_g(0, |d, _, _| {
            Ok((&[], KeyIdentifier(d)))
        })))(i)?;
        let (i, authority_cert_issuer) =
            opt(complete(parse_der_tagged_implicit_g(1, |d, _, _| {
                many0(complete(parse_generalname))(d)
            })))(i)?;
        let (i, authority_cert_serial) = opt(complete(parse_der_tagged_implicit(
            2,
            parse_der_content(DerTag::Integer),
        )))(i)?;
        let authority_cert_serial = authority_cert_serial.and_then(|o| o.as_slice().ok());
        let aki = AuthorityKeyIdentifier {
            key_identifier,
            authority_cert_issuer,
            authority_cert_serial,
        };
        Ok((i, aki))
    }

    // RFC 5280 section 4.2.1.1: Authority Key Identifier
    fn parse_authoritykeyidentifier(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (rem, aki) = parse_der_sequence_defined_g(parse_aki_content)(i)?;
        Ok((rem, ParsedExtension::AuthorityKeyIdentifier(aki)))
    }

    #[rustversion::not(since(1.37))]
    fn reverse_bits(n: u8) -> u8 {
        let mut out = 0;
        for i in 0..=7 {
            if n & (1 << i) != 0 {
                out |= 1 << (7 - i);
            }
        }
        out
    }

    #[rustversion::since(1.37)]
    #[inline]
    fn reverse_bits(n: u8) -> u8 {
        n.reverse_bits()
    }

    fn parse_keyidentifier<'a>(i: &'a [u8]) -> IResult<&'a [u8], ParsedExtension, BerError> {
        let (rest, obj) = parse_der_octetstring(i)?;
        let id = obj
            .content
            .as_slice()
            .or(Err(Err::Error(BerError::BerTypeError)))?;
        let ki = KeyIdentifier(id);
        let ret = ParsedExtension::SubjectKeyIdentifier(ki);
        Ok((rest, ret))
    }

    fn parse_keyusage(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (rest, obj) = parse_der_bitstring(i)?;
        let bitstring = obj
            .content
            .as_bitstring()
            .or(Err(Err::Error(BerError::BerTypeError)))?;
        let flags = bitstring
            .data
            .iter()
            .rev()
            .fold(0, |acc, x| acc << 8 | (reverse_bits(*x) as u16));
        Ok((rest, ParsedExtension::KeyUsage(KeyUsage { flags })))
    }

    fn parse_nscerttype(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (rest, obj) = parse_der_bitstring(i)?;
        let bitstring = obj
            .content
            .as_bitstring()
            .or(Err(Err::Error(BerError::BerTypeError)))?;
        // bitstring should be 1 byte long
        if bitstring.data.len() != 1 {
            return Err(Err::Error(BerError::BerValueError));
        }
        let flags = reverse_bits(bitstring.data[0]);
        Ok((rest, ParsedExtension::NSCertType(NSCertType(flags))))
    }

    // CertificatePolicies ::= SEQUENCE SIZE (1..MAX) OF PolicyInformation
    //
    // PolicyInformation ::= SEQUENCE {
    //      policyIdentifier   CertPolicyId,
    //      policyQualifiers   SEQUENCE SIZE (1..MAX) OF
    //              PolicyQualifierInfo OPTIONAL }
    //
    // CertPolicyId ::= OBJECT IDENTIFIER
    //
    // PolicyQualifierInfo ::= SEQUENCE {
    //      policyQualifierId  PolicyQualifierId,
    //      qualifier          ANY DEFINED BY policyQualifierId }
    //
    // -- Implementations that recognize additional policy qualifiers MUST
    // -- augment the following definition for PolicyQualifierId
    //
    // PolicyQualifierId ::= OBJECT IDENTIFIER ( id-qt-cps | id-qt-unotice )
    fn parse_certificatepolicies(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        fn parse_policy_information(i: &[u8]) -> IResult<&[u8], (Oid, &[u8]), BerError> {
            parse_der_sequence_defined_g(|content, _| {
                let (qualifier_set, oid) =
                    map_res(parse_der_oid, |x: DerObject| x.as_oid_val())(content)?;
                Ok((&[], (oid, qualifier_set)))
            })(i)
        }
        let (ret, mut policy_list) = parse_der_sequence_of_v(parse_policy_information)(i)?;
        // create the policy hashmap
        let mut policies = HashMap::new();
        for (oid, qualifier_set) in policy_list.drain(..) {
            if policies.insert(oid, qualifier_set).is_some() {
                // duplicate policies are not allowed
                return Err(Err::Failure(BerError::InvalidTag));
            }
        }
        Ok((
            ret,
            ParsedExtension::CertificatePolicies(CertificatePolicies { policies }),
        ))
    }

    // CRLReason ::= ENUMERATED { ...
    fn parse_reason_code<'a>(i: &'a [u8]) -> IResult<&'a [u8], ParsedExtension, BerError> {
        let (rest, obj) = parse_der_enum(i)?;
        let code = obj
            .content
            .as_u32()
            .or(Err(Err::Error(BerError::BerValueError)))?;
        if code > 10 {
            return Err(Err::Error(BerError::BerValueError));
        }
        let ret = ParsedExtension::ReasonCode(ReasonCode(code as u8));
        Ok((rest, ret))
    }

    // invalidityDate ::=  GeneralizedTime
    fn parse_invalidity_date<'a>(i: &'a [u8]) -> IResult<&'a [u8], ParsedExtension, BerError> {
        let (rest, date) = map_res(parse_der_generalizedtime, der_to_utctime)(i)?;
        Ok((rest, ParsedExtension::InvalidityDate(date)))
    }

    // CRLNumber ::= INTEGER (0..MAX)
    // Note from RFC 3280: "CRL verifiers MUST be able to handle CRLNumber values up to 20 octets."
    fn parse_crl_number(i: &[u8]) -> IResult<&[u8], ParsedExtension, BerError> {
        let (rest, num) = map_opt(parse_der_integer, |obj| obj.as_biguint())(i)?;
        Ok((rest, ParsedExtension::CRLNumber(num)))
    }
}

/// Extensions  ::=  SEQUENCE SIZE (1..MAX) OF Extension
pub(crate) fn parse_extension_sequence(i: &[u8]) -> X509Result<Vec<X509Extension>> {
    parse_der_sequence_defined_g(|a, _| all_consuming(many0(complete(X509Extension::from_der)))(a))(
        i,
    )
}

pub(crate) fn extensions_sequence_to_map<'a>(
    i: &'a [u8],
    v: Vec<X509Extension<'a>>,
) -> X509Result<'a, HashMap<Oid<'a>, X509Extension<'a>>> {
    let mut extensions = HashMap::new();
    for ext in v.into_iter() {
        if extensions.insert(ext.oid.clone(), ext).is_some() {
            // duplicate extensions are not allowed
            return Err(Err::Failure(X509Error::DuplicateExtensions));
        }
    }
    Ok((i, extensions))
}

pub(crate) fn parse_extensions(
    i: &[u8],
    explicit_tag: DerTag,
) -> X509Result<HashMap<Oid, X509Extension>> {
    if i.is_empty() {
        return Ok((i, HashMap::new()));
    }

    match der_read_element_header(i) {
        Ok((rem, hdr)) => {
            if hdr.tag != explicit_tag {
                return Err(Err::Error(X509Error::InvalidExtensions));
            }
            let (rem, list) = exact!(rem, parse_extension_sequence)?;
            extensions_sequence_to_map(rem, list)
        }
        Err(_) => Err(X509Error::InvalidExtensions.into()),
    }
}

fn der_read_critical(i: &[u8]) -> BerResult<bool> {
    // parse_der_optional!(i, parse_der_bool)
    let (rem, obj) = opt(parse_der_bool)(i)?;
    let value = obj
        .map(|o| o.as_bool().unwrap_or_default()) // unwrap cannot fail, we just read a bool
        .unwrap_or(false) // default critical value
        ;
    Ok((rem, value))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keyusage_flags() {
        let ku = KeyUsage { flags: 98 };
        assert!(!ku.digital_signature());
        assert!(ku.non_repudiation());
        assert!(!ku.key_encipherment());
        assert!(!ku.data_encipherment());
        assert!(!ku.key_agreement());
        assert!(ku.key_cert_sign());
        assert!(ku.crl_sign());
        assert!(!ku.encipher_only());
        assert!(!ku.decipher_only());
    }

    #[test]
    fn test_extensions1() {
        use der_parser::oid;
        let crt = crate::parse_x509_certificate(include_bytes!("../assets/extension1.der"))
            .unwrap()
            .1;
        let tbs = crt.tbs_certificate;
        assert_eq!(
            tbs.basic_constraints().unwrap().1,
            &BasicConstraints {
                ca: true,
                path_len_constraint: Some(1)
            }
        );
        {
            let ku = tbs.key_usage().unwrap().1;
            assert!(ku.digital_signature());
            assert!(!ku.non_repudiation());
            assert!(ku.key_encipherment());
            assert!(ku.data_encipherment());
            assert!(ku.key_agreement());
            assert!(!ku.key_cert_sign());
            assert!(!ku.crl_sign());
            assert!(ku.encipher_only());
            assert!(ku.decipher_only());
        }
        {
            let eku = tbs.extended_key_usage().unwrap().1;
            assert!(!eku.any);
            assert!(eku.server_auth);
            assert!(!eku.client_auth);
            assert!(eku.code_signing);
            assert!(!eku.email_protection);
            assert!(eku.time_stamping);
            assert!(!eku.ocscp_signing);
            assert_eq!(eku.other, vec![oid!(1.2.3 .4 .0 .42)]);
        }
        assert_eq!(
            tbs.policy_constraints().unwrap().1,
            &PolicyConstraints {
                require_explicit_policy: None,
                inhibit_policy_mapping: Some(10)
            }
        );
        assert_eq!(
            tbs.inhibit_anypolicy().unwrap().1,
            &InhibitAnyPolicy { skip_certs: 2 }
        );
        {
            let alt_names = &tbs.subject_alternative_name().unwrap().1.general_names;
            assert_eq!(alt_names[0], GeneralName::RFC822Name("foo@example.com"));
            assert_eq!(alt_names[1], GeneralName::URI("http://my.url.here/"));
            assert_eq!(
                alt_names[2],
                GeneralName::IPAddress([192, 168, 7, 1].as_ref())
            );
            assert_eq!(
                format!(
                    "{}",
                    match alt_names[3] {
                        GeneralName::DirectoryName(ref dn) => dn,
                        _ => unreachable!(),
                    }
                ),
                "C=UK, O=My Organization, OU=My Unit, CN=My Name"
            );
            assert_eq!(alt_names[4], GeneralName::DNSName("localhost"));
            assert_eq!(alt_names[5], GeneralName::RegisteredID(oid!(1.2.90 .0)));
            assert_eq!(
                alt_names[6],
                GeneralName::OtherName(oid!(1.2.3 .4), b"\xA0\x17\x0C\x15some other identifier")
            );
        }

        {
            let name_constraints = &tbs.name_constraints().unwrap().1;
            assert_eq!(name_constraints.permitted_subtrees, None);
            assert_eq!(
                name_constraints.excluded_subtrees,
                Some(vec![
                    GeneralSubtree {
                        base: GeneralName::IPAddress([192, 168, 0, 0, 255, 255, 0, 0].as_ref())
                    },
                    GeneralSubtree {
                        base: GeneralName::RFC822Name("foo.com")
                    },
                ])
            );
        }
    }

    #[test]
    fn test_extensions2() {
        use der_parser::oid;
        let crt = crate::parse_x509_certificate(include_bytes!("../assets/extension2.der"))
            .unwrap()
            .1;
        let tbs = crt.tbs_certificate;
        assert_eq!(
            tbs.policy_constraints().unwrap().1,
            &PolicyConstraints {
                require_explicit_policy: Some(5000),
                inhibit_policy_mapping: None
            }
        );
        {
            let pm = tbs.policy_mappings().unwrap().1;
            let mut pm_ref = HashMap::new();
            pm_ref.insert(oid!(2.34.23), vec![oid!(2.2)]);
            pm_ref.insert(oid!(1.1), vec![oid!(0.0.4)]);
            pm_ref.insert(oid!(2.2), vec![oid!(2.2.1), oid!(2.2.3)]);
            assert_eq!(pm.mappings, pm_ref);
        }
    }

    // Test cases for:
    // - parsing SubjectAlternativeName
    // - parsing NameConstraints
}
