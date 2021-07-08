//! X.509 objects and types
//!
//! Based on RFC5280
//!

use crate::error::{X509Error, X509Result};
use crate::objects::*;

use data_encoding::HEXUPPER;
use der_parser::ber::{BitStringObject, MAX_OBJECT_SIZE};
use der_parser::der::*;
use der_parser::error::*;
use der_parser::num_bigint::BigUint;
use der_parser::oid::Oid;
use der_parser::*;
use nom::branch::alt;
use nom::bytes::complete::take;
use nom::combinator::{complete, map, map_opt, map_res, opt};
use nom::multi::{many0, many1};
use nom::{Err, Offset};
use oid_registry::*;
use rusticata_macros::newtype_enum;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct X509Version(pub u32);

impl X509Version {
    // Parse [0] EXPLICIT Version DEFAULT v1
    pub(crate) fn from_der(i: &[u8]) -> X509Result<X509Version> {
        let (rem, hdr) =
            der_read_element_header(i).or(Err(Err::Error(X509Error::InvalidVersion)))?;
        match hdr.tag.0 {
            0 => {
                map(parse_der_u32, X509Version)(rem).or(Err(Err::Error(X509Error::InvalidVersion)))
            }
            _ => Ok((i, X509Version::V1)),
        }
    }

    pub(crate) fn from_der_required(i: &[u8]) -> X509Result<X509Version> {
        let (rem, hdr) =
            der_read_element_header(i).or(Err(Err::Error(X509Error::InvalidVersion)))?;
        match hdr.tag.0 {
            0 => {
                map(parse_der_u32, X509Version)(rem).or(Err(Err::Error(X509Error::InvalidVersion)))
            }
            _ => Ok((&rem[1..], X509Version::V1)),
        }
    }
}

newtype_enum! {
    impl display X509Version {
        V1 = 0,
        V2 = 1,
        V3 = 2,
    }
}

#[derive(Debug, PartialEq)]
pub struct AttributeTypeAndValue<'a> {
    pub attr_type: Oid<'a>,
    pub attr_value: DerObject<'a>, // ANY -- DEFINED BY AttributeType
}

impl<'a> AttributeTypeAndValue<'a> {
    // AttributeTypeAndValue   ::= SEQUENCE {
    //     type    AttributeType,
    //     value   AttributeValue }
    fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, attr_type) = map_res(parse_der_oid, |x: DerObject<'a>| x.as_oid_val())(i)
                .or(Err(X509Error::InvalidX509Name))?;
            let (i, attr_value) = parse_attribute_value(i).or(Err(X509Error::InvalidX509Name))?;
            let attr = AttributeTypeAndValue {
                attr_type,
                attr_value,
            };
            Ok((i, attr))
        })(i)
    }

    /// Attempt to get the content as `str`.
    /// This can fail if the object does not contain a string type.
    ///
    /// Only NumericString, PrintableString, UTF8String and IA5String
    /// are considered here. Other string types can be read using `as_slice`.
    pub fn as_str(&self) -> Result<&'a str, X509Error> {
        self.attr_value.as_str().map_err(|e| e.into())
    }

    /// Attempt to get the content as a slice.
    /// This can fail if the object does not contain a type directly equivalent to a slice (e.g a
    /// sequence).
    pub fn as_slice(&self) -> Result<&'a [u8], X509Error> {
        self.attr_value.as_slice().map_err(|e| e.into())
    }
}

// AttributeValue          ::= ANY -- DEFINED BY AttributeType
#[inline]
fn parse_attribute_value(i: &[u8]) -> DerResult {
    alt((parse_der, parse_malformed_string))(i)
}

fn parse_malformed_string(i: &[u8]) -> DerResult {
    let (rem, hdr) = der_read_element_header(i)?;
    let len = hdr.len.primitive()?;
    if len > MAX_OBJECT_SIZE {
        return Err(nom::Err::Error(BerError::InvalidLength));
    }
    match hdr.tag {
        DerTag::PrintableString => {
            // if we are in this function, the PrintableString could not be validated.
            // Accept it without validating charset, because some tools do not respect the charset
            // restrictions (for ex. they use '*' while explicingly disallowed)
            let (rem, data) = take(len as usize)(rem)?;
            let s = std::str::from_utf8(data).map_err(|_| BerError::BerValueError)?;
            let content = DerObjectContent::PrintableString(s);
            let obj = DerObject::from_header_and_content(hdr, content);
            Ok((rem, obj))
        }
        _ => Err(nom::Err::Error(BerError::InvalidTag)),
    }
}

#[derive(Debug, PartialEq)]
pub struct RelativeDistinguishedName<'a> {
    pub set: Vec<AttributeTypeAndValue<'a>>,
}

impl<'a> RelativeDistinguishedName<'a> {
    fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_set_defined_g(|i, _| {
            let (i, set) = many1(complete(AttributeTypeAndValue::from_der))(i)?;
            let rdn = RelativeDistinguishedName { set };
            Ok((i, rdn))
        })(i)
    }
}

#[derive(Debug, PartialEq)]
pub struct SubjectPublicKeyInfo<'a> {
    pub algorithm: AlgorithmIdentifier<'a>,
    pub subject_public_key: BitStringObject<'a>,
}

impl<'a> SubjectPublicKeyInfo<'a> {
    /// Parse the SubjectPublicKeyInfo struct portion of a DER-encoded X.509 Certificate
    pub fn from_der(i: &'a [u8]) -> X509Result<Self> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, algorithm) = AlgorithmIdentifier::from_der(i)?;
            let (i, subject_public_key) = map_res(parse_der_bitstring, |x: DerObject<'a>| {
                match x.content {
                    DerObjectContent::BitString(_, ref b) => Ok(b.to_owned()), // XXX padding ignored
                    _ => Err(BerError::BerTypeError),
                }
            })(i)
            .or(Err(X509Error::InvalidSPKI))?;
            let spki = SubjectPublicKeyInfo {
                algorithm,
                subject_public_key,
            };
            Ok((i, spki))
        })(i)
    }
}

#[derive(Debug, PartialEq)]
pub struct AlgorithmIdentifier<'a> {
    pub algorithm: Oid<'a>,
    pub parameters: Option<DerObject<'a>>,
}

impl<'a> AlgorithmIdentifier<'a> {
    /// Parse an algorithm identifier
    ///
    /// An algorithm identifier is defined by the following ASN.1 structure:
    ///
    /// <pre>
    /// AlgorithmIdentifier  ::=  SEQUENCE  {
    ///      algorithm               OBJECT IDENTIFIER,
    ///      parameters              ANY DEFINED BY algorithm OPTIONAL  }
    /// </pre>
    ///
    /// The algorithm identifier is used to identify a cryptographic
    /// algorithm.  The OBJECT IDENTIFIER component identifies the algorithm
    /// (such as DSA with SHA-1).  The contents of the optional parameters
    /// field will vary according to the algorithm identified.
    // lifetime is *not* useless, it is required to tell the compiler the content of the temporary
    // DerObject has the same lifetime as the input
    #[allow(clippy::needless_lifetimes)]
    pub fn from_der(i: &[u8]) -> X509Result<AlgorithmIdentifier> {
        parse_der_sequence_defined_g(|i, _| {
            let (i, algorithm) = map_res(parse_der_oid, |x| x.as_oid_val())(i)
                .or(Err(X509Error::InvalidAlgorithmIdentifier))?;
            let (i, parameters) =
                opt(complete(parse_der))(i).or(Err(X509Error::InvalidAlgorithmIdentifier))?;

            let alg = AlgorithmIdentifier {
                algorithm,
                parameters,
            };
            Ok((i, alg))
        })(i)
    }
}

#[derive(Debug, PartialEq)]
pub struct X509Name<'a> {
    pub rdn_seq: Vec<RelativeDistinguishedName<'a>>,
    pub(crate) raw: &'a [u8],
}

impl<'a> fmt::Display for X509Name<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match x509name_to_string(&self.rdn_seq) {
            Ok(o) => write!(f, "{}", o),
            Err(_) => write!(f, "<X509Error: Invalid X.509 name>"),
        }
    }
}

impl<'a> X509Name<'a> {
    /// Parse the X.501 type Name, used for ex in issuer and subject of a X.509 certificate
    pub fn from_der(i: &'a [u8]) -> X509Result<Self> {
        let start_i = i;
        parse_der_sequence_defined_g(move |i, _| {
            let (i, rdn_seq) = many0(complete(RelativeDistinguishedName::from_der))(i)?;
            let len = start_i.offset(i);
            let name = X509Name {
                rdn_seq,
                raw: &start_i[..len],
            };
            Ok((i, name))
        })(i)
    }

    // Not using the AsRef trait, as that would not give back the full 'a lifetime
    pub fn as_raw(&self) -> &'a [u8] {
        self.raw
    }

    /// Return an iterator over the `RelativeDistinguishedName` components of the name
    pub fn iter_rdn(&self) -> impl Iterator<Item = &RelativeDistinguishedName<'a>> {
        self.rdn_seq.iter()
    }

    /// Return an iterator over the attribute types and values of the name
    pub fn iter_attributes(&self) -> impl Iterator<Item = &AttributeTypeAndValue<'a>> {
        self.rdn_seq.iter().map(|rdn| rdn.set.iter()).flatten()
    }

    /// Return an iterator over the components identified by the given OID
    ///
    /// The type of the component AttributeValue is determined by the AttributeType; in
    /// general it will be a DirectoryString.
    ///
    /// Attributes with same OID may be present multiple times, so the returned object is
    /// an iterator.
    /// Expected number of objects in this iterator are
    ///   - 0: not found
    ///   - 1: present once (common case)
    ///   - 2 or more: attribute is present multiple times
    pub fn iter_by_oid(&self, oid: &Oid<'a>) -> impl Iterator<Item = &AttributeTypeAndValue<'a>> {
        // this is necessary, otherwise rustc complains
        // that caller creates a temporary value for reference (for ex.
        // `self.iter_by_oid(&OID_X509_LOCALITY_NAME)`
        // )
        let oid = oid.clone();
        self.iter_attributes()
            .filter(move |obj| obj.attr_type == oid)
    }

    /// Return an iterator over the `CommonName` attributes of the X.509 Name.
    ///
    /// Returned iterator can be empty if there are no `CommonName` attributes.
    /// If you expect only one `CommonName` to be present, then using `next()` will
    /// get an `Option<&AttributeTypeAndValue>`.
    ///
    /// A common operation is to extract the `CommonName` as a string.
    ///
    /// ```
    /// use x509_parser::x509::X509Name;
    ///
    /// fn get_first_cn_as_str<'a>(name: &'a X509Name<'_>) -> Option<&'a str> {
    ///     name.iter_common_name()
    ///         .next()
    ///         .and_then(|cn| cn.as_str().ok())
    /// }
    /// ```
    ///
    /// Note that there are multiple reasons for failure or incorrect behavior, for ex. if
    /// the attribute is present multiple times, or is not a UTF-8 encoded string (it can be
    /// UTF-16, or even an OCTETSTRING according to the standard).
    pub fn iter_common_name(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_X509_COMMON_NAME)
    }

    /// Return an iterator over the `Country` attributes of the X.509 Name.
    pub fn iter_country(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_X509_COUNTRY_NAME)
    }

    /// Return an iterator over the `Organization` attributes of the X.509 Name.
    pub fn iter_organization(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_X509_ORGANIZATION_NAME)
    }

    /// Return an iterator over the `OrganizationalUnit` attributes of the X.509 Name.
    pub fn iter_organizational_unit(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_X509_ORGANIZATIONAL_UNIT)
    }

    /// Return an iterator over the `StateOrProvinceName` attributes of the X.509 Name.
    pub fn iter_state_or_province(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_X509_STATE_OR_PROVINCE_NAME)
    }

    /// Return an iterator over the `Locality` attributes of the X.509 Name.
    pub fn iter_locality(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_X509_LOCALITY_NAME)
    }

    /// Return an iterator over the `EmailAddress` attributes of the X.509 Name.
    pub fn iter_email(&self) -> impl Iterator<Item = &AttributeTypeAndValue> {
        self.iter_by_oid(&OID_PKCS9_EMAIL_ADDRESS)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ReasonCode(pub u8);

newtype_enum! {
impl display ReasonCode {
    Unspecified = 0,
    KeyCompromise = 1,
    CACompromise = 2,
    AffiliationChanged = 3,
    Superseded = 4,
    CessationOfOperation = 5,
    CertificateHold = 6,
    // value 7 is not used
    RemoveFromCRL = 8,
    PrivilegeWithdrawn = 9,
    AACompromise = 10,
}
}

impl Default for ReasonCode {
    fn default() -> Self {
        ReasonCode::Unspecified
    }
}

// Attempt to convert attribute to string. If type is not a string, return value is the hex
// encoding of the attribute value
fn attribute_value_to_string(attr: &DerObject, _attr_type: &Oid) -> Result<String, X509Error> {
    match attr.content {
        DerObjectContent::NumericString(s)
        | DerObjectContent::PrintableString(s)
        | DerObjectContent::UTF8String(s)
        | DerObjectContent::IA5String(s) => Ok(s.to_owned()),
        _ => {
            // type is not a string, get slice and convert it to base64
            attr.as_slice()
                .map(|s| HEXUPPER.encode(s))
                .or(Err(X509Error::InvalidX509Name))
        }
    }
}

/// Convert a DER representation of a X.509 name to a human-readable string
///
/// RDNs are separated with ","
/// Multiple RDNs are separated with "+"
///
/// Attributes that cannot be represented by a string are hex-encoded
fn x509name_to_string(rdn_seq: &[RelativeDistinguishedName]) -> Result<String, X509Error> {
    rdn_seq.iter().fold(Ok(String::new()), |acc, rdn| {
        acc.and_then(|mut _vec| {
            rdn.set
                .iter()
                .fold(Ok(String::new()), |acc2, attr| {
                    acc2.and_then(|mut _vec2| {
                        let val_str = attribute_value_to_string(&attr.attr_value, &attr.attr_type)?;
                        // look ABBREV, and if not found, use shortname
                        let abbrev = match oid2abbrev(&attr.attr_type) {
                            Ok(s) => String::from(s),
                            _ => format!("{:?}", attr.attr_type),
                        };
                        let rdn = format!("{}={}", abbrev, val_str);
                        match _vec2.len() {
                            0 => Ok(rdn),
                            _ => Ok(_vec2 + " + " + &rdn),
                        }
                    })
                })
                .map(|v| match _vec.len() {
                    0 => v,
                    _ => _vec + ", " + &v,
                })
        })
    })
}

pub(crate) fn parse_signature_value(i: &[u8]) -> X509Result<BitStringObject> {
    map_res(parse_der_bitstring, |x: DerObject| {
        match x.content {
            DerObjectContent::BitString(_, ref b) => Ok(b.to_owned()), // XXX padding ignored
            _ => Err(BerError::BerTypeError),
        }
    })(i)
    .or(Err(Err::Error(X509Error::InvalidSignatureValue)))
}

pub(crate) fn parse_serial(i: &[u8]) -> X509Result<(&[u8], BigUint)> {
    map_opt(parse_der_integer, get_serial_info)(i).map_err(|_| X509Error::InvalidSerial.into())
}

fn get_serial_info(o: DerObject) -> Option<(&[u8], BigUint)> {
    let big = o.as_biguint()?;
    let slice = o.as_slice().ok()?;

    Some((slice, big))
}

#[cfg(test)]
mod tests {
    use super::*;
    use der_parser::ber::BerObjectContent;
    use der_parser::oid;

    #[test]
    fn test_x509_name() {
        let name = X509Name {
            rdn_seq: vec![
                RelativeDistinguishedName {
                    set: vec![AttributeTypeAndValue {
                        attr_type: oid!(2.5.4 .6), // countryName
                        attr_value: DerObject::from_obj(BerObjectContent::PrintableString("FR")),
                    }],
                },
                RelativeDistinguishedName {
                    set: vec![AttributeTypeAndValue {
                        attr_type: oid!(2.5.4 .8), // stateOrProvinceName
                        attr_value: DerObject::from_obj(BerObjectContent::PrintableString(
                            "Some-State",
                        )),
                    }],
                },
                RelativeDistinguishedName {
                    set: vec![AttributeTypeAndValue {
                        attr_type: oid!(2.5.4 .10), // organizationName
                        attr_value: DerObject::from_obj(BerObjectContent::PrintableString(
                            "Internet Widgits Pty Ltd",
                        )),
                    }],
                },
                RelativeDistinguishedName {
                    set: vec![
                        AttributeTypeAndValue {
                            attr_type: oid!(2.5.4 .3), // CN
                            attr_value: DerObject::from_obj(BerObjectContent::PrintableString(
                                "Test1",
                            )),
                        },
                        AttributeTypeAndValue {
                            attr_type: oid!(2.5.4 .3), // CN
                            attr_value: DerObject::from_obj(BerObjectContent::PrintableString(
                                "Test2",
                            )),
                        },
                    ],
                },
            ],
            raw: &[], // incorrect, but enough for testing
        };
        assert_eq!(
            name.to_string(),
            "C=FR, ST=Some-State, O=Internet Widgits Pty Ltd, CN=Test1 + CN=Test2"
        );
    }
}
