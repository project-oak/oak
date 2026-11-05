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

//! Validation of RFC 3161 `TimeStampToken` values embedded in PES
//! `PublicEndorsement` signatures.
//!
//! An RFC 3161 `TimeStampToken` is a CMS `ContentInfo` (`id-signedData`) whose
//! `SignedData` encapsulates a `TSTInfo` (`id-ct-TSTInfo`) and carries a
//! `SignerInfo` whose `signedAttrs` include `SigningCertificateV2`
//! (`id-aa-signingCertificateV2`). The outer layers (`ContentInfo.content` and
//! `EncapsulatedContentInfo.econtent`) borrow raw DER slices so that
//! [`verify_time_stamp_token`] can hash the exact `TSTInfo` DER octets before
//! decoding them.
//!
//! Authoritative specifications:
//! - RFC 3161 (Time-Stamp Protocol): <https://www.rfc-editor.org/rfc/rfc3161>
//! - RFC 5816 (ESSCertIDv2 Update for RFC 3161): <https://www.rfc-editor.org/rfc/rfc5816>
//! - RFC 5035 (ESS Update: Adding CertID Algorithm Agility): <https://www.rfc-editor.org/rfc/rfc5035>
//! - RFC 5652 (Cryptographic Message Syntax): <https://www.rfc-editor.org/rfc/rfc5652>
//! - RFC 5280 (Internet X.509 PKI Certificate and CRL Profile): <https://www.rfc-editor.org/rfc/rfc5280>
//! - RFC 3279 (Algorithms and Identifiers for X.509 PKI): <https://www.rfc-editor.org/rfc/rfc3279>
//! - RFC 3370 (Cryptographic Message Syntax Algorithms): <https://www.rfc-editor.org/rfc/rfc3370>
//! - RFC 4055 (Additional Algorithms and Identifiers for RSA PKCS #1): <https://www.rfc-editor.org/rfc/rfc4055>
//! - RFC 5753 (Use of ECC Algorithms in CMS): <https://www.rfc-editor.org/rfc/rfc5753>
//! - RFC 5754 (Using SHA2 Algorithms with CMS): <https://www.rfc-editor.org/rfc/rfc5754>
//! - RFC 5758 (X.509 PKI Validation for DSA and ECDSA): <https://www.rfc-editor.org/rfc/rfc5758>
//! - RFC 6211 (CMS Algorithm Identifier Protection Attribute): <https://www.rfc-editor.org/rfc/rfc6211>

// Helpers in this module are exercised by `chain_tests`, `signature_tests`,
// and `verification_tests`; the non-test library entry point
// (`verify_time_stamp_token`) is wired into `lib` in a follow-up commit, where
// this attribute is removed.
#![cfg_attr(not(test), allow(dead_code))]

use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

use chrono::{DateTime, Datelike, NaiveDateTime, Timelike, Utc};
use const_oid::{
    ObjectIdentifier,
    db::{
        rfc5280::{
            ANY_EXTENDED_KEY_USAGE, ID_CE_BASIC_CONSTRAINTS, ID_CE_EXT_KEY_USAGE, ID_CE_KEY_USAGE,
            ID_CE_SUBJECT_ALT_NAME, ID_KP_TIME_STAMPING,
        },
        rfc5911::{ID_CONTENT_TYPE, ID_MESSAGE_DIGEST, ID_SIGNED_DATA},
        rfc5912::{
            ECDSA_WITH_SHA_256, ECDSA_WITH_SHA_384, ECDSA_WITH_SHA_512, ID_EC_PUBLIC_KEY,
            ID_SHA_256, ID_SHA_384, ID_SHA_512, RSA_ENCRYPTION, SECP_256_R_1,
            SHA_256_WITH_RSA_ENCRYPTION, SHA_384_WITH_RSA_ENCRYPTION, SHA_512_WITH_RSA_ENCRYPTION,
        },
    },
};
use ecdsa::signature::hazmat::PrehashVerifier as _;
use oak_digest::{Digest, Sha256, Sha384, Sha512};
use oak_time::Instant;
use rsa::{Pkcs1v15Sign, RsaPublicKey, traits::PublicKeyParts as _};
use x509_cert::{
    Certificate, Version,
    attr::{Attribute, Attributes},
    der::{
        self, AnyRef, Choice, Decode, DecodeValue, DerOrd, Encode, EncodeValue, FixedTag, Header,
        Length, Reader, Tag, TagMode, TagNumber, Tagged, Writer,
        asn1::{
            ContextSpecific, ContextSpecificRef, IntRef, OctetString, OctetStringRef, SetOfVec,
        },
        referenced::OwnedToRef as _,
    },
    ext::{
        Extensions,
        pkix::{
            BasicConstraints, ExtendedKeyUsage, KeyUsage, SubjectAltName, SubjectKeyIdentifier,
            certpolicy::PolicyInformation,
            name::{GeneralName, GeneralNames},
        },
    },
    name::Name,
    serial_number::SerialNumber,
    spki::{AlgorithmIdentifierOwned, SubjectPublicKeyInfoOwned},
};

#[cfg(test)]
#[path = "chain_tests.rs"]
pub(crate) mod chain_tests;
#[cfg(test)]
#[path = "signature_tests.rs"]
mod signature_tests;
#[cfg(test)]
#[path = "verification_tests.rs"]
pub(crate) mod verification_tests;

/// PKCS#9 `id-ct-TSTInfo` (`1.2.840.113549.1.9.16.1.4`), RFC 3161 Section
/// 2.4.2.
pub(crate) const ID_CT_TST_INFO: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.16.1.4");

/// S/MIME `id-aa-signingCertificate` (`1.2.840.113549.1.9.16.2.12`), RFC 3161
/// Section 2.4.2 (<https://www.rfc-editor.org/rfc/rfc3161#section-2.4.2>) and
/// RFC 2634 Section 5.4 (<https://www.rfc-editor.org/rfc/rfc2634#section-5.4>).
pub(crate) const ID_AA_SIGNING_CERTIFICATE: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.16.2.12");

/// S/MIME `id-aa-signingCertificateV2` (`1.2.840.113549.1.9.16.2.47`), RFC 5816
/// Section 2.2 (updating RFC 3161 Section 2.4.2) and RFC 5035 Section 3.
pub(crate) const ID_AA_SIGNING_CERTIFICATE_V2: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.16.2.47");

/// CMS `id-aa-CMSAlgorithmProtection` (`1.2.840.113549.1.9.52`), RFC 6211
/// Section 2.
pub(crate) const ID_AA_CMS_ALGORITHM_PROTECTION: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.52");

/// Maximum certificate chain length from leaf TSA signer to root CA
/// (inclusive).
const MAX_CHAIN_DEPTH: usize = 8;

/// Maximum number of candidate issuer verifications attempted across a single
/// [`verify_certificate_chain`] invocation to bound backtracking work on cyclic
/// or duplicate certificate graphs.
const MAX_CHAIN_VERIFICATIONS: usize = 32;

/// Structured error returned when validating an RFC 3161 `TimeStampToken`.
#[allow(dead_code)]
#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum TimeStampTokenError {
    #[error("decoding ASN.1 DER: {0}")]
    Der(x509_cert::der::Error),

    #[error("empty trusted TSA root certificate list")]
    EmptyTrustedRoots,

    #[error("missing TimeStampToken in PES signature")]
    MissingTimeStampToken,

    #[error("unexpected CMS content type {0}, expected id-signedData")]
    UnexpectedContentType(ObjectIdentifier),

    #[error("unsupported SignedData version {0}, expected 3")]
    UnsupportedSignedDataVersion(u8),

    #[error("unexpected encapsulated content type {0}, expected id-ct-TSTInfo")]
    UnexpectedEncapsulatedContentType(ObjectIdentifier),

    #[error("missing encapsulated TSTInfo content")]
    MissingTstInfoContent,

    #[error("unsupported TSTInfo version {0}, expected 1")]
    UnsupportedTstInfoVersion(u8),

    #[error("invalid TSTInfo accuracy: millis and micros must be in 1 to 999")]
    InvalidTstInfoAccuracy,

    #[error("unrecognized critical extension {0} in TSTInfo")]
    UnhandledCriticalTstInfoExtension(ObjectIdentifier),

    #[error("tsa name in TSTInfo does not match TSA signer certificate subject")]
    TsaNameMismatch,

    #[error("unsupported X.509 certificate version, expected v3")]
    UnsupportedCertificateVersion,

    #[error("unrecognized critical extension {0} in certificate")]
    UnhandledCriticalCertificateExtension(ObjectIdentifier),

    #[error("missing SignerInfo in SignedData")]
    MissingSignerInfo,

    #[error("multiple SignerInfo entries in SignedData are not supported")]
    MultipleSignerInfos,

    #[error("invalid SignerInfo version {0} for SignerIdentifier")]
    InvalidSignerInfoVersion(u8),

    #[error("signer digest algorithm {0} is not listed in SignedData.digestAlgorithms")]
    DigestAlgorithmNotInSignedData(ObjectIdentifier),

    #[error("missing signedAttrs in SignerInfo")]
    MissingSignedAttrs,

    #[error("missing or invalid content-type attribute in signedAttrs")]
    InvalidSignedContentType,

    #[error("missing or invalid message-digest attribute in signedAttrs")]
    InvalidMessageDigestAttr,

    #[error("signedAttrs message-digest does not match TSTInfo digest")]
    MessageDigestMismatch,

    #[error("missing or invalid signing-certificate attribute in signedAttrs")]
    InvalidSigningCertificateAttr,

    #[error("signing-certificate attribute in signedAttrs does not match TSA signer certificate")]
    SigningCertificateMismatch,

    #[error("invalid or mismatched cmsAlgorithmProtection attribute in signedAttrs")]
    InvalidCmsAlgorithmProtection,

    #[error("messageImprint digest in TSTInfo does not match PES signature digest")]
    MessageImprintMismatch,

    #[error("unsupported digest algorithm {0}")]
    UnsupportedDigestAlgorithm(ObjectIdentifier),

    #[error("invalid parameters for digest algorithm {0}, expected absent or NULL")]
    InvalidDigestAlgorithmParameters(ObjectIdentifier),

    #[error("unsupported signature algorithm {0}")]
    UnsupportedSignatureAlgorithm(ObjectIdentifier),

    #[error("invalid parameters for signature algorithm {0}")]
    InvalidSignatureAlgorithmParameters(ObjectIdentifier),

    #[error("digest algorithm {digest_alg} is incompatible with signature algorithm {sig_alg}")]
    IncompatibleDigestAndSignatureAlgorithms {
        digest_alg: ObjectIdentifier,
        sig_alg: ObjectIdentifier,
    },

    #[error("no TSA signer certificate matching SignerIdentifier found in token")]
    SignerCertificateNotFound,

    #[error("signer certificate missing critical ExtendedKeyUsage with id-kp-timeStamping")]
    MissingTimeStampingExtendedKeyUsage,

    #[error("signer certificate must not be a CA certificate")]
    SignerCertificateIsCa,

    #[error("signer certificate KeyUsage does not permit digitalSignature")]
    MissingSignerDigitalSignatureKeyUsage,

    #[error("invalid cryptographic signature: {0}")]
    SignatureVerification(String),

    #[error("certificate is not valid at timestamp generation time")]
    CertificateValidityPeriod,

    #[error("timestamp generation time is outside PES certificate validity period")]
    IssuanceTimeOutsidePesCertValidity,

    #[error("issuer certificate missing BasicConstraints with cA=true")]
    MissingCaBasicConstraints,

    #[error("issuer certificate pathLenConstraint exceeded")]
    PathLenConstraintExceeded,

    #[error("issuer certificate KeyUsage does not permit keyCertSign")]
    MissingKeyCertSignKeyUsage,

    #[error("issuer certificate ExtendedKeyUsage does not permit id-kp-timeStamping")]
    InvalidCaExtendedKeyUsage,

    #[error("no valid certificate chain from TSA signer certificate to a trusted TSA root")]
    UntrustedCertificateChain,
}

// `#[from]` cannot be used on `TimeStampTokenError::Der` because `#[from]`
// implies `#[source]`, which requires `core::error::Error`, and `x509-cert`
// (`der` 0.7) only implements `Error` for `der::Error` when its `std` feature
// is enabled.
impl From<x509_cert::der::Error> for TimeStampTokenError {
    fn from(err: x509_cert::der::Error) -> Self {
        Self::Der(err)
    }
}

macro_rules! seq_len {
    ($($item:expr),* $(,)?) => {{
        let mut total = Length::ZERO;
        $(
            total = (total + $item)?;
        )*
        Ok(total)
    }};
}

fn decode_explicit_required<'a, R: Reader<'a>, T: Decode<'a>>(
    reader: &mut R,
    tag_number: TagNumber,
) -> der::Result<T> {
    ContextSpecific::<T>::decode_explicit(reader, tag_number)?
        .map(|cs| cs.value)
        .ok_or_else(|| Tag::ContextSpecific { constructed: true, number: tag_number }.value_error())
}

fn explicit_len<T: EncodeValue + Tagged>(tag_number: TagNumber, value: &T) -> der::Result<Length> {
    ContextSpecificRef { tag_number, tag_mode: TagMode::Explicit, value }.encoded_len()
}

fn encode_explicit<W: Writer, T: EncodeValue + Tagged>(
    writer: &mut W,
    tag_number: TagNumber,
    value: &T,
) -> der::Result<()> {
    ContextSpecificRef { tag_number, tag_mode: TagMode::Explicit, value }.encode(writer)
}

fn decode_explicit_optional<'a, R: Reader<'a>, T: Decode<'a>>(
    reader: &mut R,
    tag_number: TagNumber,
) -> der::Result<Option<T>> {
    Ok(ContextSpecific::<T>::decode_explicit(reader, tag_number)?.map(|cs| cs.value))
}

fn explicit_optional_len<T: EncodeValue + Tagged>(
    tag_number: TagNumber,
    value: &Option<T>,
) -> der::Result<Length> {
    match value {
        Some(v) => explicit_len(tag_number, v),
        None => Ok(Length::ZERO),
    }
}

fn encode_explicit_optional<W: Writer, T: EncodeValue + Tagged>(
    writer: &mut W,
    tag_number: TagNumber,
    value: &Option<T>,
) -> der::Result<()> {
    if let Some(v) = value {
        encode_explicit(writer, tag_number, v)?;
    }
    Ok(())
}

fn decode_implicit_optional<'a, R: Reader<'a>, T: DecodeValue<'a> + FixedTag>(
    reader: &mut R,
    tag_number: TagNumber,
) -> der::Result<Option<T>> {
    Ok(ContextSpecific::<T>::decode_implicit(reader, tag_number)?.map(|cs| cs.value))
}

fn implicit_optional_len<T: EncodeValue + Tagged>(
    tag_number: TagNumber,
    value: &Option<T>,
) -> der::Result<Length> {
    match value {
        Some(v) => {
            ContextSpecificRef { tag_number, tag_mode: TagMode::Implicit, value: v }.encoded_len()
        }
        None => Ok(Length::ZERO),
    }
}

fn encode_implicit_optional<W: Writer, T: EncodeValue + Tagged>(
    writer: &mut W,
    tag_number: TagNumber,
    value: &Option<T>,
) -> der::Result<()> {
    if let Some(v) = value {
        ContextSpecificRef { tag_number, tag_mode: TagMode::Implicit, value: v }.encode(writer)?;
    }
    Ok(())
}

/// CMS `ContentInfo` structure (RFC 5652 Section 3).
///
/// Named `ContentInfo` because RFC 3161 Section 2.4.2 defines
/// `TimeStampToken ::= ContentInfo` (where `contentType` is `id-signedData`
/// and `content` is `SignedData`):
/// <https://www.rfc-editor.org/rfc/rfc3161#section-2.4.2>.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ContentInfo<'a> {
    pub content_type: ObjectIdentifier,
    pub content: AnyRef<'a>,
}

impl FixedTag for ContentInfo<'_> {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for ContentInfo<'a> {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self {
                content_type: reader.decode()?,
                content: decode_explicit_required(reader, TagNumber::N0)?,
            })
        })
    }
}

impl EncodeValue for ContentInfo<'_> {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(self.content_type.encoded_len()?, explicit_len(TagNumber::N0, &self.content)?)
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.content_type.encode(writer)?;
        encode_explicit(writer, TagNumber::N0, &self.content)
    }
}

/// CMS `SignedData` structure (RFC 5652 Section 5.1).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedData<'a> {
    pub version: u8,
    pub digest_algorithms: SetOfVec<AlgorithmIdentifierOwned>,
    pub encap_content_info: EncapsulatedContentInfo<'a>,
    /// X.509 certificates carried in `SignedData.certificates`
    /// (`[0] IMPLICIT CertificateSet OPTIONAL`).
    ///
    /// Note:
    /// - Decoded into `Vec<Certificate>` rather than `SetOfVec<Certificate>` so
    ///   that wire order (typically leaf -> intermediate -> root chain order in
    ///   RFC 3161 TSA tokens) is preserved for lossless DER round-tripping and
    ///   duplicate certificates do not fail `SetOfVec` validation.
    /// - RFC 5652 Section 10.2.2 defines `CertificateSet ::= SET OF
    ///   CertificateChoices`, which also includes context-tagged attribute and
    ///   non-X.509 certificate variants (`[0]`–`[3]`). This field is
    ///   intentionally restricted to X.509 `Certificate` elements, as PES TSA
    ///   verification only supports X.509 PKI certificate chains.
    pub certificates: Option<Vec<Certificate>>,
    pub crls: Option<SetOfVec<AnyRef<'a>>>,
    pub signer_infos: SetOfVec<SignerInfo>,
}

impl FixedTag for SignedData<'_> {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for SignedData<'a> {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self {
                version: reader.decode()?,
                digest_algorithms: reader.decode()?,
                encap_content_info: reader.decode()?,
                certificates: decode_implicit_optional(reader, TagNumber::N0)?,
                crls: decode_implicit_optional(reader, TagNumber::N1)?,
                signer_infos: reader.decode()?,
            })
        })
    }
}

impl EncodeValue for SignedData<'_> {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(
            self.version.encoded_len()?,
            self.digest_algorithms.encoded_len()?,
            self.encap_content_info.encoded_len()?,
            implicit_optional_len(TagNumber::N0, &self.certificates)?,
            implicit_optional_len(TagNumber::N1, &self.crls)?,
            self.signer_infos.encoded_len()?,
        )
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.version.encode(writer)?;
        self.digest_algorithms.encode(writer)?;
        self.encap_content_info.encode(writer)?;
        encode_implicit_optional(writer, TagNumber::N0, &self.certificates)?;
        encode_implicit_optional(writer, TagNumber::N1, &self.crls)?;
        self.signer_infos.encode(writer)
    }
}

/// CMS `EncapsulatedContentInfo` structure (RFC 5652 Section 5.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EncapsulatedContentInfo<'a> {
    pub econtent_type: ObjectIdentifier,
    pub econtent: Option<OctetStringRef<'a>>,
}

impl FixedTag for EncapsulatedContentInfo<'_> {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for EncapsulatedContentInfo<'a> {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self {
                econtent_type: reader.decode()?,
                econtent: decode_explicit_optional(reader, TagNumber::N0)?,
            })
        })
    }
}

impl EncodeValue for EncapsulatedContentInfo<'_> {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(
            self.econtent_type.encoded_len()?,
            explicit_optional_len(TagNumber::N0, &self.econtent)?,
        )
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.econtent_type.encode(writer)?;
        encode_explicit_optional(writer, TagNumber::N0, &self.econtent)
    }
}

/// CMS `IssuerAndSerialNumber` structure (RFC 5652 Section 10.2.4).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IssuerAndSerialNumber {
    pub issuer: Name,
    pub serial_number: SerialNumber,
}

impl FixedTag for IssuerAndSerialNumber {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for IssuerAndSerialNumber {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self { issuer: reader.decode()?, serial_number: reader.decode()? })
        })
    }
}

impl EncodeValue for IssuerAndSerialNumber {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(self.issuer.encoded_len()?, self.serial_number.encoded_len()?)
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.issuer.encode(writer)?;
        self.serial_number.encode(writer)
    }
}

/// CMS `SignerIdentifier` choice (RFC 5652 Section 5.3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SignerIdentifier {
    IssuerAndSerialNumber(IssuerAndSerialNumber),
    SubjectKeyIdentifier(OctetString),
}

const SIGNER_SKI_TAG: Tag = Tag::ContextSpecific { constructed: false, number: TagNumber::N0 };

impl<'a> Choice<'a> for SignerIdentifier {
    fn can_decode(tag: Tag) -> bool {
        tag == Tag::Sequence || tag == SIGNER_SKI_TAG
    }
}

impl<'a> Decode<'a> for SignerIdentifier {
    fn decode<R: Reader<'a>>(reader: &mut R) -> der::Result<Self> {
        match reader.peek_tag()? {
            Tag::Sequence => Ok(Self::IssuerAndSerialNumber(reader.decode()?)),
            SIGNER_SKI_TAG => {
                let cs = ContextSpecific::<OctetString>::decode_implicit(reader, TagNumber::N0)?
                    .ok_or_else(|| SIGNER_SKI_TAG.value_error())?;
                Ok(Self::SubjectKeyIdentifier(cs.value))
            }
            actual => {
                Err(der::Error::from(der::ErrorKind::TagUnexpected { expected: None, actual }))
            }
        }
    }
}

impl Tagged for SignerIdentifier {
    fn tag(&self) -> Tag {
        match self {
            Self::IssuerAndSerialNumber(_) => Tag::Sequence,
            Self::SubjectKeyIdentifier(_) => SIGNER_SKI_TAG,
        }
    }
}

impl EncodeValue for SignerIdentifier {
    fn value_len(&self) -> der::Result<Length> {
        match self {
            Self::IssuerAndSerialNumber(iasn) => iasn.value_len(),
            Self::SubjectKeyIdentifier(ski) => ski.value_len(),
        }
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        match self {
            Self::IssuerAndSerialNumber(iasn) => iasn.encode_value(writer),
            Self::SubjectKeyIdentifier(ski) => ski.encode_value(writer),
        }
    }
}

/// CMS `SignerInfo` structure (RFC 5652 Section 5.3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignerInfo {
    pub version: u8,
    pub sid: SignerIdentifier,
    pub digest_algorithm: AlgorithmIdentifierOwned,
    pub signed_attrs: Option<Attributes>,
    pub signature_algorithm: AlgorithmIdentifierOwned,
    pub signature: OctetString,
    pub unsigned_attrs: Option<Attributes>,
}

impl FixedTag for SignerInfo {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for SignerInfo {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self {
                version: reader.decode()?,
                sid: reader.decode()?,
                digest_algorithm: reader.decode()?,
                signed_attrs: decode_implicit_optional(reader, TagNumber::N0)?,
                signature_algorithm: reader.decode()?,
                signature: reader.decode()?,
                unsigned_attrs: decode_implicit_optional(reader, TagNumber::N1)?,
            })
        })
    }
}

impl EncodeValue for SignerInfo {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(
            self.version.encoded_len()?,
            self.sid.encoded_len()?,
            self.digest_algorithm.encoded_len()?,
            implicit_optional_len(TagNumber::N0, &self.signed_attrs)?,
            self.signature_algorithm.encoded_len()?,
            self.signature.encoded_len()?,
            implicit_optional_len(TagNumber::N1, &self.unsigned_attrs)?,
        )
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.version.encode(writer)?;
        self.sid.encode(writer)?;
        self.digest_algorithm.encode(writer)?;
        encode_implicit_optional(writer, TagNumber::N0, &self.signed_attrs)?;
        self.signature_algorithm.encode(writer)?;
        self.signature.encode(writer)?;
        encode_implicit_optional(writer, TagNumber::N1, &self.unsigned_attrs)
    }
}

impl DerOrd for SignerInfo {
    fn der_cmp(&self, other: &Self) -> der::Result<core::cmp::Ordering> {
        Ok(self.to_der()?.cmp(&other.to_der()?))
    }
}

/// RFC 5035 `SigningCertificateV2` structure (RFC 5035 Section 3, required by
/// RFC 5816 Section 2.2 updating RFC 3161 Section 2.4.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SigningCertificateV2 {
    pub certs: Vec<EssCertIdV2>,
    pub policies: Option<Vec<PolicyInformation>>,
}

impl FixedTag for SigningCertificateV2 {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for SigningCertificateV2 {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self { certs: reader.decode()?, policies: reader.decode()? })
        })
    }
}

impl EncodeValue for SigningCertificateV2 {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(self.certs.encoded_len()?, self.policies.encoded_len()?)
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.certs.encode(writer)?;
        self.policies.encode(writer)
    }
}

/// RFC 5035 `IssuerSerial` structure (RFC 5035 Section 4).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IssuerSerial {
    pub issuer: GeneralNames,
    pub serial_number: SerialNumber,
}

impl FixedTag for IssuerSerial {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for IssuerSerial {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self { issuer: reader.decode()?, serial_number: reader.decode()? })
        })
    }
}

impl EncodeValue for IssuerSerial {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(self.issuer.encoded_len()?, self.serial_number.encoded_len()?)
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.issuer.encode(writer)?;
        self.serial_number.encode(writer)
    }
}

/// Returns the RFC 5035 Section 4 default `hashAlgorithm`
/// (`{ algorithm id-sha256 }`, with `parameters: None`).
fn default_ess_hash_algorithm() -> AlgorithmIdentifierOwned {
    AlgorithmIdentifierOwned { oid: ID_SHA_256, parameters: None }
}

/// Checks whether `alg` equals the RFC 5035 Section 4 ASN.1 default
/// `{ algorithm id-sha256 }` (`parameters: None`).
fn is_default_ess_hash_algorithm(alg: &AlgorithmIdentifierOwned) -> bool {
    alg.oid == ID_SHA_256 && alg.parameters.is_none()
}

/// RFC 5035 `ESSCertIDv2` structure (RFC 5035 Section 4, required by RFC 5816
/// Section 2.2 updating RFC 3161 Section 2.4.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EssCertIdV2 {
    /// Hash algorithm used to compute `cert_hash`.
    ///
    /// RFC 5035 Section 4 defines `hashAlgorithm AlgorithmIdentifier DEFAULT
    /// {algorithm id-sha256}`. Per ITU-T X.690 Section 11.5, the default value
    /// (`oid: ID_SHA_256, parameters: None`) is omitted when encoding to DER,
    /// populated when omitted during decoding, and rejected if explicitly
    /// encoded in DER.
    ///
    /// Note on explicit `NULL` parameters: `decode_value` permits an explicit
    /// `{ algorithm id-sha256, parameters NULL }` (`parameters:
    /// Some(Any::null())`) because its wire encoding differs from the ASN.1
    /// default `{ algorithm id-sha256 }`. Downstream verification must
    /// validate `AlgorithmIdentifier.parameters` (accepting only `None` or
    /// `Some(Any::null())`).
    pub hash_algorithm: AlgorithmIdentifierOwned,
    pub cert_hash: OctetString,
    pub issuer_serial: Option<IssuerSerial>,
}

impl FixedTag for EssCertIdV2 {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for EssCertIdV2 {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            let decoded_alg: Option<AlgorithmIdentifierOwned> = reader.decode()?;
            // RFC 5035 Section 4 defines `hashAlgorithm DEFAULT {algorithm id-sha256}`.
            // Per ITU-T X.690 Section 11.5, default values MUST be omitted in DER.
            if decoded_alg.as_ref().is_some_and(is_default_ess_hash_algorithm) {
                return Err(Tag::Sequence.value_error());
            }
            Ok(Self {
                hash_algorithm: decoded_alg.unwrap_or_else(default_ess_hash_algorithm),
                cert_hash: reader.decode()?,
                issuer_serial: reader.decode()?,
            })
        })
    }
}

impl EncodeValue for EssCertIdV2 {
    fn value_len(&self) -> der::Result<Length> {
        let hash_alg_len = if is_default_ess_hash_algorithm(&self.hash_algorithm) {
            Length::ZERO
        } else {
            self.hash_algorithm.encoded_len()?
        };
        seq_len!(hash_alg_len, self.cert_hash.encoded_len()?, self.issuer_serial.encoded_len()?)
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        if !is_default_ess_hash_algorithm(&self.hash_algorithm) {
            self.hash_algorithm.encode(writer)?;
        }
        self.cert_hash.encode(writer)?;
        self.issuer_serial.encode(writer)
    }
}

/// RFC 6211 `CMSAlgorithmProtection` attribute structure (RFC 6211 Section 2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CmsAlgorithmProtection {
    pub digest_algorithm: AlgorithmIdentifierOwned,
    pub signature_algorithm: Option<AlgorithmIdentifierOwned>,
    pub mac_algorithm: Option<AlgorithmIdentifierOwned>,
}

impl FixedTag for CmsAlgorithmProtection {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for CmsAlgorithmProtection {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self {
                digest_algorithm: reader.decode()?,
                signature_algorithm: decode_implicit_optional(reader, TagNumber::N1)?,
                mac_algorithm: decode_implicit_optional(reader, TagNumber::N2)?,
            })
        })
    }
}

impl EncodeValue for CmsAlgorithmProtection {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(
            self.digest_algorithm.encoded_len()?,
            implicit_optional_len(TagNumber::N1, &self.signature_algorithm)?,
            implicit_optional_len(TagNumber::N2, &self.mac_algorithm)?,
        )
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.digest_algorithm.encode(writer)?;
        encode_implicit_optional(writer, TagNumber::N1, &self.signature_algorithm)?;
        encode_implicit_optional(writer, TagNumber::N2, &self.mac_algorithm)
    }
}

/// RFC 3161 `MessageImprint` structure (RFC 3161 Section 2.4.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MessageImprint {
    pub hash_algorithm: AlgorithmIdentifierOwned,
    pub hashed_message: OctetString,
}

impl FixedTag for MessageImprint {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for MessageImprint {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self { hash_algorithm: reader.decode()?, hashed_message: reader.decode()? })
        })
    }
}

impl EncodeValue for MessageImprint {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(self.hash_algorithm.encoded_len()?, self.hashed_message.encoded_len()?)
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.hash_algorithm.encode(writer)?;
        self.hashed_message.encode(writer)
    }
}

/// RFC 3161 `Accuracy` structure (RFC 3161 Section 2.4.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Accuracy {
    pub seconds: Option<u64>,
    pub millis: Option<u16>,
    pub micros: Option<u16>,
}

impl FixedTag for Accuracy {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for Accuracy {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            Ok(Self {
                seconds: reader.decode()?,
                millis: decode_implicit_optional(reader, TagNumber::N0)?,
                micros: decode_implicit_optional(reader, TagNumber::N1)?,
            })
        })
    }
}

impl EncodeValue for Accuracy {
    fn value_len(&self) -> der::Result<Length> {
        seq_len!(
            self.seconds.encoded_len()?,
            implicit_optional_len(TagNumber::N0, &self.millis)?,
            implicit_optional_len(TagNumber::N1, &self.micros)?,
        )
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        self.seconds.encode(writer)?;
        encode_implicit_optional(writer, TagNumber::N0, &self.millis)?;
        encode_implicit_optional(writer, TagNumber::N1, &self.micros)
    }
}

/// RFC 3161 `TSTInfo` structure (RFC 3161 Section 2.4.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TstInfo<'a> {
    pub version: u8,
    pub policy: ObjectIdentifier,
    pub message_imprint: MessageImprint,
    pub serial_number: SerialNumber,
    pub gen_time: Rfc3161GeneralizedTime,
    pub accuracy: Option<Accuracy>,
    // RFC 3161 Section 2.4.2 defines `ordering BOOLEAN DEFAULT FALSE`.
    // Per X.690 Section 11.5 (DER), a DEFAULT FALSE value is omitted when false.
    pub ordering: bool,
    // RFC 3161 Section 2.4.2 defines `nonce INTEGER OPTIONAL` as an arbitrary
    // ASN.1 INTEGER without RFC 5280's 20-octet positive SerialNumber limit.
    pub nonce: Option<IntRef<'a>>,
    pub tsa: Option<GeneralName>,
    pub extensions: Option<Extensions>,
}

impl FixedTag for TstInfo<'_> {
    const TAG: Tag = Tag::Sequence;
}

impl<'a> DecodeValue<'a> for TstInfo<'a> {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        reader.read_nested(header.length, |reader| {
            let version = reader.decode()?;
            let policy = reader.decode()?;
            let message_imprint = reader.decode()?;
            let serial_number = reader.decode()?;
            let gen_time = reader.decode()?;
            let accuracy = reader.decode()?;
            // Per X.690 Section 11.5 (DER), DEFAULT FALSE must be omitted when false.
            let ordering = match reader.decode::<Option<bool>>()? {
                Some(true) => true,
                Some(false) => return Err(Tag::Boolean.value_error()),
                None => false,
            };
            let nonce = reader.decode()?;
            let tsa = decode_explicit_optional(reader, TagNumber::N0)?;
            let extensions = decode_implicit_optional(reader, TagNumber::N1)?;
            Ok(Self {
                version,
                policy,
                message_imprint,
                serial_number,
                gen_time,
                accuracy,
                ordering,
                nonce,
                tsa,
                extensions,
            })
        })
    }
}

impl EncodeValue for TstInfo<'_> {
    fn value_len(&self) -> der::Result<Length> {
        let ordering_opt = if self.ordering { Some(true) } else { None };
        seq_len!(
            self.version.encoded_len()?,
            self.policy.encoded_len()?,
            self.message_imprint.encoded_len()?,
            self.serial_number.encoded_len()?,
            self.gen_time.encoded_len()?,
            self.accuracy.encoded_len()?,
            ordering_opt.encoded_len()?,
            self.nonce.encoded_len()?,
            explicit_optional_len(TagNumber::N0, &self.tsa)?,
            implicit_optional_len(TagNumber::N1, &self.extensions)?,
        )
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        let ordering_opt = if self.ordering { Some(true) } else { None };
        self.version.encode(writer)?;
        self.policy.encode(writer)?;
        self.message_imprint.encode(writer)?;
        self.serial_number.encode(writer)?;
        self.gen_time.encode(writer)?;
        self.accuracy.encode(writer)?;
        ordering_opt.encode(writer)?;
        self.nonce.encode(writer)?;
        encode_explicit_optional(writer, TagNumber::N0, &self.tsa)?;
        encode_implicit_optional(writer, TagNumber::N1, &self.extensions)
    }
}

/// RFC 3161 `GeneralizedTime` (`YYYYMMDDHHMMSS[.f...]Z`), which allows
/// fractional seconds (up to nanosecond precision) unlike X.509
/// `GeneralizedTime` (RFC 3161 Section 2.4.2).
///
/// Note: `x509_cert::der::asn1::GeneralizedTime` enforces RFC 5280 Section
/// 4.1.2.5.2 (requiring an exact 15-byte `YYYYMMDDHHMMSSZ` encoding and
/// rejecting fractional seconds), so a dedicated decoder/encoder is required
/// for RFC 3161 Section 2.4.2. Because [`Instant`] has nanosecond precision,
/// fractional seconds with more than 9 digits are rejected during decoding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Rfc3161GeneralizedTime(pub Instant);

impl Rfc3161GeneralizedTime {
    fn to_utc_datetime(self) -> der::Result<(DateTime<Utc>, u32)> {
        const NANOS_PER_SEC: i128 = 1_000_000_000;
        let total_nanos = self.0.into_unix_nanos();
        let seconds = i64::try_from(total_nanos.div_euclid(NANOS_PER_SEC))
            .map_err(|_| Tag::GeneralizedTime.value_error())?;
        let nanos = u32::try_from(total_nanos.rem_euclid(NANOS_PER_SEC))
            .map_err(|_| Tag::GeneralizedTime.value_error())?;
        let dt = DateTime::<Utc>::from_timestamp(seconds, nanos)
            .ok_or_else(|| Tag::GeneralizedTime.value_error())?;
        if !(0..=9999).contains(&dt.year()) {
            return Err(Tag::GeneralizedTime.value_error());
        }
        Ok((dt, nanos))
    }

    fn to_generalized_time_string(self) -> der::Result<String> {
        let (dt, nanos) = self.to_utc_datetime()?;
        let prefix = format!(
            "{:04}{:02}{:02}{:02}{:02}{:02}",
            dt.year(),
            dt.month(),
            dt.day(),
            dt.hour(),
            dt.minute(),
            dt.second()
        );
        if nanos == 0 {
            Ok(format!("{prefix}Z"))
        } else {
            let frac = format!("{nanos:09}");
            Ok(format!("{prefix}.{}Z", frac.trim_end_matches('0')))
        }
    }
}

impl FixedTag for Rfc3161GeneralizedTime {
    const TAG: Tag = Tag::GeneralizedTime;
}

impl<'a> DecodeValue<'a> for Rfc3161GeneralizedTime {
    fn decode_value<R: Reader<'a>>(reader: &mut R, header: Header) -> der::Result<Self> {
        let bytes = reader.read_slice(header.length)?;
        let s = core::str::from_utf8(bytes).map_err(|_| Tag::GeneralizedTime.value_error())?;
        // RFC 3161 Section 2.4.2 requires GeneralizedTime in UTC with exact
        // 14-digit "YYYYMMDDHHMMSS[.f...]Z" syntax and no trailing zeroes in
        // the fractional seconds component. ITU-T X.680 Section 46.3 restricts
        // seconds to 00..=59 (rejecting "60", which chrono's `%S` accepts as a
        // leap second).
        if s.len() < 15
            || !s.ends_with('Z')
            || !s.as_bytes()[..14].iter().all(u8::is_ascii_digit)
            || &s[12..14] > "59"
        {
            return Err(Tag::GeneralizedTime.value_error());
        }
        if s.len() > 15 {
            let frac = &s.as_bytes()[15..s.len() - 1];
            if s.as_bytes()[14] != b'.'
                || frac.is_empty()
                || frac.len() > 9
                || !frac.iter().all(u8::is_ascii_digit)
                || frac.ends_with(b"0")
            {
                return Err(Tag::GeneralizedTime.value_error());
            }
        }
        let dt = NaiveDateTime::parse_from_str(s, "%Y%m%d%H%M%S%.fZ")
            .map_err(|_| Tag::GeneralizedTime.value_error())?;
        Ok(Self(Instant::from(dt.and_utc())))
    }
}

impl EncodeValue for Rfc3161GeneralizedTime {
    fn value_len(&self) -> der::Result<Length> {
        let (_, mut nanos) = self.to_utc_datetime()?;
        if nanos == 0 {
            return Ok(Length::new(15));
        }
        let mut frac_digits = 9u16;
        while nanos.is_multiple_of(10) {
            nanos /= 10;
            frac_digits -= 1;
        }
        Ok(Length::new(16 + frac_digits))
    }

    fn encode_value(&self, writer: &mut impl Writer) -> der::Result<()> {
        let encoded = self.to_generalized_time_string()?;
        writer.write(encoded.as_bytes())
    }
}

/// Minimum accepted RSA public key modulus length in bits (256 bytes), per
/// NIST SP 800-57 Part 1 Rev. 5
/// (<https://csrc.nist.gov/pubs/sp/800/57/pt1/r5/final>).
const MIN_RSA_MODULUS_BITS: usize = 2048;

fn has_absent_or_null_params(alg: &AlgorithmIdentifierOwned) -> bool {
    alg.parameters.as_ref().is_none_or(|params| params.is_null())
}

/// Supported hash algorithms for RFC 3161 digests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DigestAlgorithm {
    Sha256,
    Sha384,
    Sha512,
}

impl DigestAlgorithm {
    /// Parses and validates a SHA-2 `AlgorithmIdentifier` per RFC 5754 Section
    /// 2 (<https://www.rfc-editor.org/rfc/rfc5754#section-2>), accepting only
    /// absent or ASN.1 `NULL` parameters.
    fn from_algorithm(alg: &AlgorithmIdentifierOwned) -> Result<Self, TimeStampTokenError> {
        let digest_alg = match alg.oid {
            ID_SHA_256 => Self::Sha256,
            ID_SHA_384 => Self::Sha384,
            ID_SHA_512 => Self::Sha512,
            oid => return Err(TimeStampTokenError::UnsupportedDigestAlgorithm(oid)),
        };
        if !has_absent_or_null_params(alg) {
            return Err(TimeStampTokenError::InvalidDigestAlgorithmParameters(alg.oid));
        }
        Ok(digest_alg)
    }

    fn digest(self, data: &[u8]) -> Digest {
        match self {
            Self::Sha256 => Digest::Sha256(Sha256::from_contents(data)),
            Self::Sha384 => Digest::Sha384(Sha384::from_contents(data)),
            Self::Sha512 => Digest::Sha512(Sha512::from_contents(data)),
        }
    }
}

/// Supported signature algorithms for RFC 3161 CMS `SignerInfo` and X.509
/// certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SignatureAlgorithm {
    RsaPkcs1v15(DigestAlgorithm),
    Ecdsa(DigestAlgorithm),
}

impl SignatureAlgorithm {
    /// Parses and validates an X.509 signature `AlgorithmIdentifier` per:
    /// - RFC 3279 (<https://www.rfc-editor.org/rfc/rfc3279>)
    /// - RFC 4055 Section 5 (<https://www.rfc-editor.org/rfc/rfc4055#section-5>)
    /// - RFC 5758 Section 3.2 (<https://www.rfc-editor.org/rfc/rfc5758#section-3.2>)
    fn from_x509_algorithm(
        sig_alg: &AlgorithmIdentifierOwned,
    ) -> Result<Self, TimeStampTokenError> {
        match sig_alg.oid {
            SHA_256_WITH_RSA_ENCRYPTION => Self::rsa_from_params(DigestAlgorithm::Sha256, sig_alg),
            SHA_384_WITH_RSA_ENCRYPTION => Self::rsa_from_params(DigestAlgorithm::Sha384, sig_alg),
            SHA_512_WITH_RSA_ENCRYPTION => Self::rsa_from_params(DigestAlgorithm::Sha512, sig_alg),
            ECDSA_WITH_SHA_256 => Self::ecdsa_from_x509_params(DigestAlgorithm::Sha256, sig_alg),
            ECDSA_WITH_SHA_384 => Self::ecdsa_from_x509_params(DigestAlgorithm::Sha384, sig_alg),
            ECDSA_WITH_SHA_512 => Self::ecdsa_from_x509_params(DigestAlgorithm::Sha512, sig_alg),
            oid => Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(oid)),
        }
    }

    /// Resolves and validates a CMS `(digestAlgorithm, signatureAlgorithm)`
    /// pair per:
    /// - RFC 5652 Section 5.3 (<https://www.rfc-editor.org/rfc/rfc5652#section-5.3>)
    /// - RFC 3370 Section 3.2 (<https://www.rfc-editor.org/rfc/rfc3370#section-3.2>)
    /// - RFC 5753 Section 2.1.1 (<https://www.rfc-editor.org/rfc/rfc5753#section-2.1.1>)
    /// - RFC 5754 Section 3 (<https://www.rfc-editor.org/rfc/rfc5754#section-3>)
    ///
    /// Deviations for legacy PKCS#7/CMS interoperability:
    /// - Accepts absent parameters (in addition to `NULL`) on `rsaEncryption`
    ///   in `SignerInfo.signatureAlgorithm` (RFC 3370 Section 3.2 specifies
    ///   `NULL`).
    /// - Accepts `id-ecPublicKey` (with absent or `NULL` parameters) in
    ///   `SignerInfo.signatureAlgorithm` as a fallback for legacy PKCS#7/CMS
    ///   signers that emit the public-key OID alongside `digestAlgorithm`
    ///   instead of a combined `ecdsa-with-SHA*` OID as required by RFC 5753
    ///   Section 2.1.1.
    fn from_cms_algorithms(
        digest_alg_id: &AlgorithmIdentifierOwned,
        sig_alg: &AlgorithmIdentifierOwned,
    ) -> Result<Self, TimeStampTokenError> {
        let digest_alg = DigestAlgorithm::from_algorithm(digest_alg_id)?;
        match sig_alg.oid {
            RSA_ENCRYPTION => Self::rsa_from_params(digest_alg, sig_alg),
            // Non-RFC legacy PKCS#7/CMS compatibility fallback (not permitted
            // by RFC 5753 Section 2.1.1, which requires `ecdsa-with-SHA*`).
            ID_EC_PUBLIC_KEY => {
                if !has_absent_or_null_params(sig_alg) {
                    return Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(
                        sig_alg.oid,
                    ));
                }
                Ok(Self::Ecdsa(digest_alg))
            }
            _ => {
                let parsed = Self::from_x509_algorithm(sig_alg)?;
                if parsed.digest_algorithm() != digest_alg {
                    return Err(TimeStampTokenError::IncompatibleDigestAndSignatureAlgorithms {
                        digest_alg: digest_alg_id.oid,
                        sig_alg: sig_alg.oid,
                    });
                }
                Ok(parsed)
            }
        }
    }

    fn digest_algorithm(self) -> DigestAlgorithm {
        match self {
            Self::RsaPkcs1v15(digest_alg) | Self::Ecdsa(digest_alg) => digest_alg,
        }
    }

    fn rsa_from_params(
        digest_alg: DigestAlgorithm,
        sig_alg: &AlgorithmIdentifierOwned,
    ) -> Result<Self, TimeStampTokenError> {
        if !has_absent_or_null_params(sig_alg) {
            return Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(sig_alg.oid));
        }
        Ok(Self::RsaPkcs1v15(digest_alg))
    }

    fn ecdsa_from_x509_params(
        digest_alg: DigestAlgorithm,
        sig_alg: &AlgorithmIdentifierOwned,
    ) -> Result<Self, TimeStampTokenError> {
        if sig_alg.parameters.is_some() {
            return Err(TimeStampTokenError::InvalidSignatureAlgorithmParameters(sig_alg.oid));
        }
        Ok(Self::Ecdsa(digest_alg))
    }
}

/// Verifies a signature over `message` against an X.509
/// `SubjectPublicKeyInfoOwned` for RSA PKCS#1 v1.5 (SHA-256/384/512) and ECDSA
/// P-256 (SHA-256/384/512) per:
/// - RFC 3279 (<https://www.rfc-editor.org/rfc/rfc3279>)
/// - RFC 4055 (<https://www.rfc-editor.org/rfc/rfc4055>)
/// - RFC 5758 (<https://www.rfc-editor.org/rfc/rfc5758>)
fn verify_spki_signature(
    spki: &SubjectPublicKeyInfoOwned,
    sig_alg: SignatureAlgorithm,
    message: &[u8],
    signature_bytes: &[u8],
) -> Result<(), TimeStampTokenError> {
    let spki_ref = spki.owned_to_ref();

    match sig_alg {
        SignatureAlgorithm::RsaPkcs1v15(digest_alg) => {
            if spki.algorithm.oid != RSA_ENCRYPTION {
                return Err(TimeStampTokenError::SignatureVerification(
                    "expected rsaEncryption SPKI algorithm".to_string(),
                ));
            }
            let rsa_key = RsaPublicKey::try_from(spki_ref)
                .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))?;
            if rsa_key.n().bits() < MIN_RSA_MODULUS_BITS {
                return Err(TimeStampTokenError::SignatureVerification(format!(
                    "RSA modulus too small: {} bits, minimum is {MIN_RSA_MODULUS_BITS}",
                    rsa_key.n().bits()
                )));
            }
            let digest = digest_alg.digest(message);
            let verify_res = match digest_alg {
                DigestAlgorithm::Sha256 => rsa_key.verify(
                    Pkcs1v15Sign::new::<sha2::Sha256>(),
                    digest.as_ref(),
                    signature_bytes,
                ),
                DigestAlgorithm::Sha384 => rsa_key.verify(
                    Pkcs1v15Sign::new::<sha2::Sha384>(),
                    digest.as_ref(),
                    signature_bytes,
                ),
                DigestAlgorithm::Sha512 => rsa_key.verify(
                    Pkcs1v15Sign::new::<sha2::Sha512>(),
                    digest.as_ref(),
                    signature_bytes,
                ),
            };
            verify_res.map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))
        }
        SignatureAlgorithm::Ecdsa(digest_alg) => {
            if spki.algorithm.oid != ID_EC_PUBLIC_KEY {
                return Err(TimeStampTokenError::SignatureVerification(
                    "expected id-ecPublicKey SPKI algorithm".to_string(),
                ));
            }
            let curve_oid = spki
                .algorithm
                .parameters
                .as_ref()
                .ok_or_else(|| {
                    TimeStampTokenError::SignatureVerification(
                        "missing EC curve parameters".to_string(),
                    )
                })?
                .decode_as::<ObjectIdentifier>()
                .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))?;
            // Note: P-384 (`secp384r1`) is intentionally omitted for now to avoid
            // adding a `p384` crate dependency to `pes`.
            match curve_oid {
                SECP_256_R_1 => {
                    let vk = p256::ecdsa::VerifyingKey::try_from(spki_ref)
                        .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))?;
                    let sig = p256::ecdsa::Signature::from_der(signature_bytes)
                        .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))?;
                    // `ecdsa::VerifyingKey::verify_prehash` converts `digest` to a field
                    // element via `ecdsa::hazmat::bits2field` per RFC 6979 Section 2.3.2
                    // (<https://www.rfc-editor.org/rfc/rfc6979#section-2.3.2>), truncating
                    // digests wider than the curve's field (e.g. SHA-384 or SHA-512 with
                    // P-256).
                    let digest = digest_alg.digest(message);
                    vk.verify_prehash(digest.as_ref(), &sig)
                        .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))
                }
                _ => Err(TimeStampTokenError::SignatureVerification(format!(
                    "unsupported EC curve {curve_oid}"
                ))),
            }
        }
    }
}

/// Verifies that `subject` was cryptographically signed by `issuer`'s public
/// key per RFC 5280 Section 4.1.1.2
/// (<https://www.rfc-editor.org/rfc/rfc5280#section-4.1.1.2>).
fn verify_certificate_signature(
    subject: &Certificate,
    issuer: &Certificate,
) -> Result<(), TimeStampTokenError> {
    if subject.tbs_certificate.signature != subject.signature_algorithm {
        return Err(TimeStampTokenError::SignatureVerification(
            "certificate tbsCertificate.signature does not match signatureAlgorithm".to_string(),
        ));
    }
    let sig_alg = SignatureAlgorithm::from_x509_algorithm(&subject.signature_algorithm)?;
    let signature_bytes = subject.signature.as_bytes().ok_or_else(|| {
        TimeStampTokenError::SignatureVerification(
            "certificate signature BIT STRING has non-zero unused bits".to_string(),
        )
    })?;
    let tbs_der = subject.tbs_certificate.to_der()?;
    verify_spki_signature(
        &issuer.tbs_certificate.subject_public_key_info,
        sig_alg,
        &tbs_der,
        signature_bytes,
    )
}

/// Parses DER-encoded X.509 certificates for use as trusted TSA root anchors.
pub fn parse_tsa_root_certs(
    tsa_root_certs_der: &[Vec<u8>],
) -> Result<Vec<Certificate>, TimeStampTokenError> {
    tsa_root_certs_der
        .iter()
        .map(|der_bytes| Certificate::from_der(der_bytes).map_err(TimeStampTokenError::from))
        .collect()
}

/// Validates a DER-encoded RFC 3161 `TimeStampToken` from a PES
/// `PublicEndorsement`.
///
/// Validation performs the following checks:
/// 1. Parses the CMS `ContentInfo` (`id-signedData`), `SignedData` (`version ==
///    5` when `crls` contains `OtherRevocationInfoFormat`, or `3` otherwise),
///    and encapsulated `TSTInfo` (`id-ct-TSTInfo`, `version == 1`, valid
///    `accuracy`, and no unrecognized critical or duplicate extensions) per
///    <https://www.rfc-editor.org/rfc/rfc3161#section-2.4.2> and
///    <https://www.rfc-editor.org/rfc/rfc5652#section-5.1>.
/// 2. Validates the single `SignerInfo` (`version` matching `sid`, supported
///    `digestAlgorithm` present in `SignedData.digestAlgorithms`, and
///    compatible `signatureAlgorithm`) and verifies that
///    `SignerInfo.signedAttrs` contains single-valued `content-type` equal to
///    `id-ct-TSTInfo`, `message-digest` equal to the digest of the raw
///    `TSTInfo` DER bytes, `id-aa-signingCertificateV2` (`ESSCertIDv2`), and
///    (when present) matching `id-aa-CMSAlgorithmProtection` per
///    <https://www.rfc-editor.org/rfc/rfc3161#section-2.4.2>,
///    <https://www.rfc-editor.org/rfc/rfc5816#section-2.2>, and
///    <https://www.rfc-editor.org/rfc/rfc6211#section-2>.
/// 3. Locates candidate TSA signer certificates in `SignedData.certificates`
///    matching `SignerInfo.sid`, resolves the signer certificate matching the
///    `ESSCertIDv2` (`certHash` and optional `issuerSerial`), verifies that it
///    matches `TSTInfo.tsa` (when present, against `tbsCertificate.subject` or
///    `SubjectAltName`), and checks that the signer certificate is an X.509 v3
///    end-entity certificate (`BasicConstraints.ca != true`) without
///    unrecognized critical extensions, whose `KeyUsage` (if present) permits
///    `digitalSignature` or `nonRepudiation`, and that it contains a critical
///    `ExtendedKeyUsage` extension with only `id-kp-timeStamping`
///    (`1.3.6.1.5.5.7.3.8`) per
///    <https://www.rfc-editor.org/rfc/rfc3161#section-2.3>.
/// 4. Verifies the CMS signature over `SignerInfo.signedAttrs` using the TSA
///    signer certificate's public key.
/// 5. Validates the X.509 certificate chain from the TSA signer certificate to
///    one of the provided `tsa_root_certs` at the timestamp's `genTime`
///    (checking signatures, validity periods, `BasicConstraints`, `KeyUsage`,
///    `ExtendedKeyUsage`, and critical extensions).
/// 6. Verifies that the timestamp issuance time (`TSTInfo.genTime`) falls
///    within the validity period of `pes_cert`.
/// 7. Verifies that the `TSTInfo.messageImprint` hash matches the digest of
///    `pes_signature`.
pub fn verify_time_stamp_token(
    token_der: &[u8],
    pes_signature: &[u8],
    pes_cert: &Certificate,
    tsa_root_certs: &[Certificate],
) -> Result<(), TimeStampTokenError> {
    if tsa_root_certs.is_empty() {
        return Err(TimeStampTokenError::EmptyTrustedRoots);
    }

    // 1. Parse CMS ContentInfo -> SignedData -> TSTInfo per RFC 3161 Section 2.4.2.
    let content_info = ContentInfo::from_der(token_der)?;
    if content_info.content_type != ID_SIGNED_DATA {
        return Err(TimeStampTokenError::UnexpectedContentType(content_info.content_type));
    }
    let signed_data = content_info.content.decode_as::<SignedData<'_>>()?;
    // RFC 3161 Section 2.4.2 & RFC 5652 Section 5.1: SignedData.version must be
    // 5 when SignedData.crls contains any [1] IMPLICIT OtherRevocationInfoFormat
    // entry, and 3 otherwise (because eContentType is id-ct-TSTInfo, other than
    // id-data, and only X.509 certificates are permitted).
    const OTHER_REVOCATION_INFO_TAG: Tag =
        Tag::ContextSpecific { constructed: true, number: TagNumber::N1 };
    let has_other_crl = signed_data
        .crls
        .as_ref()
        .is_some_and(|crls| crls.iter().any(|crl| crl.tag() == OTHER_REVOCATION_INFO_TAG));
    let expected_sd_version = if has_other_crl { 5 } else { 3 };
    if signed_data.version != expected_sd_version {
        return Err(TimeStampTokenError::UnsupportedSignedDataVersion(signed_data.version));
    }
    if signed_data.encap_content_info.econtent_type != ID_CT_TST_INFO {
        return Err(TimeStampTokenError::UnexpectedEncapsulatedContentType(
            signed_data.encap_content_info.econtent_type,
        ));
    }
    let tst_info_der = signed_data
        .encap_content_info
        .econtent
        .ok_or(TimeStampTokenError::MissingTstInfoContent)?
        .as_bytes();
    let tst_info = TstInfo::from_der(tst_info_der)?;
    // RFC 3161 Section 2.4.2: `version INTEGER { v1(1) }`.
    if tst_info.version != 1 {
        return Err(TimeStampTokenError::UnsupportedTstInfoVersion(tst_info.version));
    }
    // RFC 3161 Section 2.4.2: `millis [0] INTEGER (1..999) OPTIONAL`,
    // `micros [1] INTEGER (1..999) OPTIONAL`.
    if let Some(ref accuracy) = tst_info.accuracy
        && (accuracy.millis.is_some_and(|m| !(1..=999).contains(&m))
            || accuracy.micros.is_some_and(|u| !(1..=999).contains(&u)))
    {
        return Err(TimeStampTokenError::InvalidTstInfoAccuracy);
    }
    // RFC 3161 Section 2.4.2 & RFC 5280 Section 4.2: Extensions (when present)
    // is `SEQUENCE SIZE (1..MAX) OF Extension` without duplicate extension OIDs,
    // and any unrecognized critical extension in TSTInfo must be rejected.
    if let Some(ref extensions) = tst_info.extensions {
        if extensions.is_empty() {
            return Err(TimeStampTokenError::Der(der::ErrorKind::Failed.into()));
        }
        for (i, ext) in extensions.iter().enumerate() {
            if extensions[..i].iter().any(|prev| prev.extn_id == ext.extn_id) {
                return Err(TimeStampTokenError::Der(der::ErrorKind::Failed.into()));
            }
            if ext.critical {
                return Err(TimeStampTokenError::UnhandledCriticalTstInfoExtension(ext.extn_id));
            }
        }
    }

    // 2. Validate SignerInfo and signedAttrs (independent of candidate signer
    //    certificates).
    let signer_info = match signed_data.signer_infos.as_slice() {
        [] => return Err(TimeStampTokenError::MissingSignerInfo),
        [single] => single,
        _ => return Err(TimeStampTokenError::MultipleSignerInfos),
    };

    // RFC 3161 Section 2.4.2 & RFC 5652 Section 5.3: SignerInfo.version must be
    // 1 when SignerIdentifier is IssuerAndSerialNumber and 3 when it is
    // SubjectKeyIdentifier.
    let expected_si_version = match signer_info.sid {
        SignerIdentifier::IssuerAndSerialNumber(_) => 1,
        SignerIdentifier::SubjectKeyIdentifier(_) => 3,
    };
    if signer_info.version != expected_si_version {
        return Err(TimeStampTokenError::InvalidSignerInfoVersion(signer_info.version));
    }

    let signer_digest_alg = DigestAlgorithm::from_algorithm(&signer_info.digest_algorithm)?;
    // RFC 3161 Section 2.4.2 & RFC 5652 Section 5.1: SignerInfo.digestAlgorithm
    // must be included among SignedData.digestAlgorithms.
    if !signed_data
        .digest_algorithms
        .iter()
        .any(|alg| alg.oid == signer_info.digest_algorithm.oid && has_absent_or_null_params(alg))
    {
        return Err(TimeStampTokenError::DigestAlgorithmNotInSignedData(
            signer_info.digest_algorithm.oid,
        ));
    }

    let cms_sig_alg = SignatureAlgorithm::from_cms_algorithms(
        &signer_info.digest_algorithm,
        &signer_info.signature_algorithm,
    )?;

    let signed_attrs =
        signer_info.signed_attrs.as_ref().ok_or(TimeStampTokenError::MissingSignedAttrs)?;
    let (ess_cert_id, cert_digest_alg) = verify_signed_attrs(
        signed_attrs,
        signer_digest_alg,
        &signer_info.digest_algorithm,
        &signer_info.signature_algorithm,
        tst_info_der,
    )?;
    let signed_attrs_der = signed_attrs.to_der()?;

    // 3a. Locate candidate TSA signer certificates matching SignerInfo.sid and
    //     resolve the single certificate matching ESSCertIDv2 in signedAttrs
    //     (certHash and optional IssuerSerial) per RFC 5816 Section 2.2 and RFC
    //     5035 Sections 3–4.
    let certificates = signed_data.certificates.as_deref().unwrap_or(&[]);
    let signer_candidates = find_signer_certificates(certificates, &signer_info.sid)?;
    let signer_cert = signer_candidates
        .into_iter()
        .find_map(|cert| match verify_ess_cert_id(&ess_cert_id, cert_digest_alg, cert) {
            Ok(()) => Some(Ok(cert)),
            Err(TimeStampTokenError::SigningCertificateMismatch) => None,
            Err(err) => Some(Err(err)),
        })
        .transpose()?
        .ok_or(TimeStampTokenError::SigningCertificateMismatch)?;

    // 3b. If TSTInfo.tsa is present, verify that it matches one of the TSA
    //     signer certificate's subject names per RFC 3161 Section 2.4.2.
    if let Some(ref tsa_name) = tst_info.tsa {
        verify_tsa_name(tsa_name, signer_cert)?;
    }

    // 3c. Validate TSA signer certificate extensions per RFC 3161 Section 2.3
    //     and RFC 5280 Sections 4.2, 4.2.1.3, 4.2.1.6, 4.2.1.9, 4.2.1.12.
    verify_signer_cert_extensions(signer_cert)?;

    // 4. Verify CMS signature over DER-encoded signedAttrs (encoded as SET OF
    //    Attribute per RFC 5652 Section 5.4).
    verify_spki_signature(
        &signer_cert.tbs_certificate.subject_public_key_info,
        cms_sig_alg,
        &signed_attrs_der,
        signer_info.signature.as_bytes(),
    )?;

    // 5. Verify TSA certificate chain against tsa_root_certs at tst_info.gen_time.
    let gen_time = tst_info.gen_time.0;
    verify_certificate_chain(signer_cert, certificates, tsa_root_certs, gen_time)?;

    // 6. Verify that tst_info.gen_time is within the PES certificate's validity
    //    period.
    // Note: This check should be performed on the PES root certificate and
    // replaced in a follow-up change.
    verify_cert_validity_contains(pes_cert, gen_time)
        .map_err(|_| TimeStampTokenError::IssuanceTimeOutsidePesCertValidity)?;

    // 7. Verify TSTInfo.messageImprint against the PES signature bytes per RFC 3161
    //    Section 2.4.2.
    let imprint_digest_alg =
        DigestAlgorithm::from_algorithm(&tst_info.message_imprint.hash_algorithm)?;
    let expected_imprint = imprint_digest_alg.digest(pes_signature);
    if tst_info.message_imprint.hashed_message.as_bytes() != expected_imprint.as_ref() {
        return Err(TimeStampTokenError::MessageImprintMismatch);
    }

    Ok(())
}

fn decode_single_attr_value<'a, T: DecodeValue<'a> + FixedTag>(
    attr: &'a Attribute,
    is_duplicate: bool,
    err: TimeStampTokenError,
) -> Result<T, TimeStampTokenError> {
    let [raw] = attr.values.as_slice() else {
        return Err(err);
    };
    if is_duplicate {
        return Err(err);
    }
    raw.decode_as::<T>().map_err(|_| err)
}

/// Validates CMS `SignedAttributes` on the `TimeStampToken` `SignerInfo` (RFC
/// 3161 Section 2.4.2, RFC 5816 Section 2.2, RFC 5035 Sections 3–4, RFC 5652
/// Sections 5.3 and 11.1–11.2, and RFC 6211 Section 2):
/// - No attribute OID may appear more than once, and every attribute must have
///   at least one value (`SET SIZE (1..MAX) OF AttributeValue`).
/// - `content-type` (`id-contentType`) must be single-valued and equal
///   `id-ct-TSTInfo`.
/// - `message-digest` (`id-messageDigest`) must be single-valued and match the
///   digest of `tst_info_der`.
/// - `signing-certificate-v2` (`id-aa-signingCertificateV2`) must be present
///   and single-valued, and its first `ESSCertIDv2` entry must have a supported
///   hash algorithm.
/// - If `id-aa-signingCertificate` is present, it must be single-valued.
/// - If `id-aa-CMSAlgorithmProtection` is present, it must be single-valued,
///   omit `macAlgorithm`, and match `signer_digest_alg_id` and
///   `signer_sig_alg_id`.
///
/// Returns the first [`EssCertIdV2`] and its resolved [`DigestAlgorithm`] for
/// matching against candidate TSA signer certificates via
/// [`verify_ess_cert_id`].
fn verify_signed_attrs(
    attrs: &Attributes,
    signer_digest_alg: DigestAlgorithm,
    signer_digest_alg_id: &AlgorithmIdentifierOwned,
    signer_sig_alg_id: &AlgorithmIdentifierOwned,
    tst_info_der: &[u8],
) -> Result<(EssCertIdV2, DigestAlgorithm), TimeStampTokenError> {
    let mut found_content_type = false;
    let mut message_digest: Option<OctetString> = None;
    let mut signing_cert_v2: Option<SigningCertificateV2> = None;

    let attrs_slice = attrs.as_slice();
    for (i, attr) in attrs_slice.iter().enumerate() {
        let is_duplicate = attrs_slice[..i].iter().any(|prev| prev.oid == attr.oid);
        if attr.oid == ID_CONTENT_TYPE {
            let content_type: ObjectIdentifier = decode_single_attr_value(
                attr,
                is_duplicate,
                TimeStampTokenError::InvalidSignedContentType,
            )?;
            if content_type != ID_CT_TST_INFO {
                return Err(TimeStampTokenError::InvalidSignedContentType);
            }
            found_content_type = true;
        } else if attr.oid == ID_MESSAGE_DIGEST {
            message_digest = Some(decode_single_attr_value(
                attr,
                is_duplicate,
                TimeStampTokenError::InvalidMessageDigestAttr,
            )?);
        } else if attr.oid == ID_AA_SIGNING_CERTIFICATE_V2 {
            // RFC 5816 Section 2.2 (updating RFC 3161 Section 2.4.2) & RFC 5035
            // Section 3: SigningCertificateV2 is a single-valued signed
            // attribute binding the TSA signer certificate hash.
            signing_cert_v2 = Some(decode_single_attr_value(
                attr,
                is_duplicate,
                TimeStampTokenError::InvalidSigningCertificateAttr,
            )?);
        } else if attr.oid == ID_AA_SIGNING_CERTIFICATE {
            // RFC 3161 Section 2.4.2 allows legacy SigningCertificate alongside
            // SigningCertificateV2, but it must be single-valued if present.
            if is_duplicate || attr.values.len() != 1 {
                return Err(TimeStampTokenError::InvalidSigningCertificateAttr);
            }
        } else if attr.oid == ID_AA_CMS_ALGORITHM_PROTECTION {
            // RFC 6211 Section 2: cmsAlgorithmProtection is a single-valued
            // attribute whose digestAlgorithm and signatureAlgorithm must match
            // SignerInfo (and macAlgorithm must be absent for SignedData).
            let cap: CmsAlgorithmProtection = decode_single_attr_value(
                attr,
                is_duplicate,
                TimeStampTokenError::InvalidCmsAlgorithmProtection,
            )?;
            if &cap.digest_algorithm != signer_digest_alg_id
                || cap.signature_algorithm.as_ref() != Some(signer_sig_alg_id)
                || cap.mac_algorithm.is_some()
            {
                return Err(TimeStampTokenError::InvalidCmsAlgorithmProtection);
            }
        } else if is_duplicate || attr.values.is_empty() {
            // RFC 5652 Section 5.3: SignedAttributes must not contain multiple
            // instances of the same attribute type, and each Attribute must
            // carry a non-empty SET OF AttributeValue.
            return Err(TimeStampTokenError::Der(der::ErrorKind::Failed.into()));
        }
    }

    if !found_content_type {
        return Err(TimeStampTokenError::InvalidSignedContentType);
    }
    let message_digest_attr =
        message_digest.ok_or(TimeStampTokenError::InvalidMessageDigestAttr)?;
    let expected_tst_digest = signer_digest_alg.digest(tst_info_der);
    if message_digest_attr.as_bytes() != expected_tst_digest.as_ref() {
        return Err(TimeStampTokenError::MessageDigestMismatch);
    }

    let signing_cert_v2 =
        signing_cert_v2.ok_or(TimeStampTokenError::InvalidSigningCertificateAttr)?;
    // RFC 5035 Section 3: "The first certificate identified in the sequence of
    // certificate identifiers MUST be the certificate used to verify the
    // signature."
    let ess_cert_id = signing_cert_v2
        .certs
        .into_iter()
        .next()
        .ok_or(TimeStampTokenError::InvalidSigningCertificateAttr)?;
    let cert_digest_alg = DigestAlgorithm::from_algorithm(&ess_cert_id.hash_algorithm)?;

    Ok((ess_cert_id, cert_digest_alg))
}

/// Verifies that `ess_cert_id` (`ESSCertIDv2`) matches `signer_cert`'s DER
/// bytes and optional `IssuerSerial` per RFC 3161 Section 2.4.2, RFC 5816
/// Section 2.2, and RFC 5035 Sections 3–4.
fn verify_ess_cert_id(
    ess_cert_id: &EssCertIdV2,
    cert_digest_alg: DigestAlgorithm,
    signer_cert: &Certificate,
) -> Result<(), TimeStampTokenError> {
    let signer_cert_der = signer_cert.to_der()?;
    let expected_cert_hash = cert_digest_alg.digest(&signer_cert_der);
    if ess_cert_id.cert_hash.as_bytes() != expected_cert_hash.as_ref() {
        return Err(TimeStampTokenError::SigningCertificateMismatch);
    }
    // RFC 5035 Section 4: "If present, the issuerSerial field MUST match the
    // issuer and serialNumber fields of the certificate."
    if let Some(ref issuer_serial) = ess_cert_id.issuer_serial {
        let issuer_matches = match issuer_serial.issuer.as_slice() {
            [GeneralName::DirectoryName(dir_name)] => {
                dir_name == &signer_cert.tbs_certificate.issuer
            }
            _ => false,
        };
        if !issuer_matches
            || issuer_serial.serial_number != signer_cert.tbs_certificate.serial_number
        {
            return Err(TimeStampTokenError::SigningCertificateMismatch);
        }
    }

    Ok(())
}

/// Verifies that `TSTInfo.tsa` matches one of the subject names (`subject` or
/// `SubjectAltName`) in the TSA signer certificate per:
/// - RFC 3161 Section 2.4.2 (<https://www.rfc-editor.org/rfc/rfc3161#section-2.4.2>)
/// - RFC 5280 Section 4.2.1.6 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.6>)
fn verify_tsa_name(
    tsa_name: &GeneralName,
    signer_cert: &Certificate,
) -> Result<(), TimeStampTokenError> {
    if matches!(tsa_name, GeneralName::DirectoryName(dir_name) if dir_name.0.is_empty()) {
        return Err(TimeStampTokenError::TsaNameMismatch);
    }
    if let GeneralName::DirectoryName(dir_name) = tsa_name
        && dir_name == &signer_cert.tbs_certificate.subject
    {
        return Ok(());
    }
    if let Some((_critical, SubjectAltName(alt_names))) =
        signer_cert.tbs_certificate.get::<SubjectAltName>()?
        && alt_names.iter().any(|alt_name| alt_name == tsa_name)
    {
        return Ok(());
    }
    Err(TimeStampTokenError::TsaNameMismatch)
}

/// Finds all candidate TSA signer certificates in `certificates` matching `sid`
/// per RFC 5652 Section 5.3 (<https://www.rfc-editor.org/rfc/rfc5652#section-5.3>)
/// and RFC 5280 Section 4.2.1.2
/// (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.2>).
///
/// Multiple certificates may match when `sid` is
/// [`SignerIdentifier::SubjectKeyIdentifier`] (for example, when a token
/// bundles both an older and a renewed TSA signer certificate sharing the same
/// public key). Returns [`TimeStampTokenError::SignerCertificateNotFound`] if
/// no certificate matches `sid`.
fn find_signer_certificates<'a>(
    certificates: &'a [Certificate],
    sid: &SignerIdentifier,
) -> Result<Vec<&'a Certificate>, TimeStampTokenError> {
    let mut matches = Vec::new();
    for cert in certificates {
        match sid {
            SignerIdentifier::IssuerAndSerialNumber(iasn) => {
                if cert.tbs_certificate.issuer == iasn.issuer
                    && cert.tbs_certificate.serial_number == iasn.serial_number
                {
                    matches.push(cert);
                }
            }
            SignerIdentifier::SubjectKeyIdentifier(expected_ski) => {
                if let Some((_critical, SubjectKeyIdentifier(ski))) =
                    cert.tbs_certificate.get::<SubjectKeyIdentifier>()?
                    && &ski == expected_ski
                {
                    matches.push(cert);
                }
            }
        }
    }
    if matches.is_empty() {
        return Err(TimeStampTokenError::SignerCertificateNotFound);
    }
    Ok(matches)
}

/// Verifies that `cert` is an X.509 v3 certificate without duplicate extension
/// OIDs or unrecognized critical extensions per:
/// - RFC 5280 Section 4.1.2.1 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.1.2.1>)
/// - RFC 5280 Section 4.2 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2>)
fn verify_v3_and_critical_extensions(
    cert: &Certificate,
    allowed_critical_oids: &[ObjectIdentifier],
) -> Result<(), TimeStampTokenError> {
    if cert.tbs_certificate.version != Version::V3 {
        return Err(TimeStampTokenError::UnsupportedCertificateVersion);
    }
    if let Some(ref extensions) = cert.tbs_certificate.extensions {
        for (i, ext) in extensions.iter().enumerate() {
            if extensions[..i].iter().any(|prev| prev.extn_id == ext.extn_id) {
                return Err(TimeStampTokenError::Der(der::ErrorKind::Failed.into()));
            }
            if ext.critical && !allowed_critical_oids.contains(&ext.extn_id) {
                return Err(TimeStampTokenError::UnhandledCriticalCertificateExtension(
                    ext.extn_id,
                ));
            }
        }
    }
    Ok(())
}

/// Verifies version and extensions on the leaf TSA signer certificate per:
/// - RFC 3161 Section 2.3 (<https://www.rfc-editor.org/rfc/rfc3161#section-2.3>)
/// - RFC 5280 Section 4.2 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2>)
/// - RFC 5280 Section 4.2.1.3 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.3>)
/// - RFC 5280 Section 4.2.1.6 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.6>)
/// - RFC 5280 Section 4.2.1.9 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.9>)
/// - RFC 5280 Section 4.2.1.12 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.12>)
///
/// Specifically:
/// - Certificate `version` must be `v3` and no unrecognized critical extensions
///   may be present.
/// - `ExtendedKeyUsage` must be present, critical, and contain only
///   `id-kp-timeStamping`.
/// - `BasicConstraints` (if present) must not have `cA=true`.
/// - `KeyUsage` (if present) must permit `digitalSignature` or
///   `nonRepudiation`.
fn verify_signer_cert_extensions(cert: &Certificate) -> Result<(), TimeStampTokenError> {
    verify_v3_and_critical_extensions(
        cert,
        &[ID_CE_EXT_KEY_USAGE, ID_CE_BASIC_CONSTRAINTS, ID_CE_KEY_USAGE, ID_CE_SUBJECT_ALT_NAME],
    )?;

    match cert.tbs_certificate.get::<ExtendedKeyUsage>()? {
        Some((true, ExtendedKeyUsage(oids))) if oids.as_slice() == [ID_KP_TIME_STAMPING] => {}
        _ => return Err(TimeStampTokenError::MissingTimeStampingExtendedKeyUsage),
    }

    if let Some((_critical, basic_constraints)) = cert.tbs_certificate.get::<BasicConstraints>()?
        && basic_constraints.ca
    {
        return Err(TimeStampTokenError::SignerCertificateIsCa);
    }

    if let Some((_critical, key_usage)) = cert.tbs_certificate.get::<KeyUsage>()?
        && !key_usage.digital_signature()
        && !key_usage.non_repudiation()
    {
        return Err(TimeStampTokenError::MissingSignerDigitalSignatureKeyUsage);
    }

    Ok(())
}

/// Validates the X.509 certificate chain from `signer_cert` up to a trust
/// anchor in `tsa_root_certs` at `validation_time` per:
/// - RFC 3161 Section 2.3 (<https://www.rfc-editor.org/rfc/rfc3161#section-2.3>)
/// - RFC 5280 Section 6.1 (<https://www.rfc-editor.org/rfc/rfc5280#section-6.1>)
///
/// Uses depth-first search with backtracking bounded by both
/// [`MAX_CHAIN_DEPTH`] and [`MAX_CHAIN_VERIFICATIONS`] so that tokens bundling
/// cross-signed or multiple candidate intermediate certificates resolve a valid
/// path when one exists without risking exponential path-building blowup.
fn verify_certificate_chain(
    signer_cert: &Certificate,
    token_certs: &[Certificate],
    tsa_root_certs: &[Certificate],
    validation_time: Instant,
) -> Result<(), TimeStampTokenError> {
    if tsa_root_certs.is_empty() {
        return Err(TimeStampTokenError::EmptyTrustedRoots);
    }
    verify_cert_validity_contains(signer_cert, validation_time)?;
    if tsa_root_certs.contains(signer_cert) {
        return Ok(());
    }

    let mut visited: Vec<&Certificate> = Vec::with_capacity(MAX_CHAIN_DEPTH - 1);
    visited.push(signer_cert);
    let mut remaining_verifications = MAX_CHAIN_VERIFICATIONS;
    verify_certificate_chain_recursive(
        signer_cert,
        token_certs,
        tsa_root_certs,
        validation_time,
        0,
        &mut visited,
        &mut remaining_verifications,
    )
}

fn record_direct_err(slot: &mut Option<TimeStampTokenError>, err: TimeStampTokenError) {
    if slot.is_none() || !matches!(err, TimeStampTokenError::SignatureVerification(_)) {
        *slot = Some(err);
    }
}

fn record_branch_err(slot: &mut Option<TimeStampTokenError>, err: TimeStampTokenError) {
    if slot.is_none() || !matches!(err, TimeStampTokenError::UntrustedCertificateChain) {
        *slot = Some(err);
    }
}

fn verify_certificate_chain_recursive<'a>(
    current_cert: &'a Certificate,
    token_certs: &'a [Certificate],
    tsa_root_certs: &'a [Certificate],
    validation_time: Instant,
    non_self_issued_intermediates: usize,
    visited: &mut Vec<&'a Certificate>,
    remaining_verifications: &mut usize,
) -> Result<(), TimeStampTokenError> {
    // 1. Check if current_cert was directly issued and signed by a trusted root
    //    anchor in tsa_root_certs.
    let mut root_err: Option<TimeStampTokenError> = None;
    for root in tsa_root_certs {
        if root.tbs_certificate.subject != current_cert.tbs_certificate.issuer {
            continue;
        }
        if *remaining_verifications == 0 {
            break;
        }
        *remaining_verifications -= 1;
        match verify_issuer(current_cert, root, validation_time, non_self_issued_intermediates) {
            Ok(()) => return Ok(()),
            Err(err) => record_direct_err(&mut root_err, err),
        }
    }

    // Adding another intermediate requires at least `visited.len() + 2`
    // certificates (`visited` + `candidate` + `root`), which would exceed
    // `MAX_CHAIN_DEPTH`.
    if visited.len() >= MAX_CHAIN_DEPTH - 1 {
        return Err(root_err.unwrap_or(TimeStampTokenError::UntrustedCertificateChain));
    }

    // 2. Otherwise, try candidate intermediate issuers in token_certs with bounded
    //    backtracking.
    let mut verified_branch_err: Option<TimeStampTokenError> = None;
    let mut candidate_err: Option<TimeStampTokenError> = None;
    for candidate in token_certs {
        if *remaining_verifications == 0 {
            break;
        }
        if visited.contains(&candidate) || tsa_root_certs.contains(candidate) {
            continue;
        }
        if candidate.tbs_certificate.subject != current_cert.tbs_certificate.issuer {
            continue;
        }
        *remaining_verifications -= 1;
        match verify_issuer(current_cert, candidate, validation_time, non_self_issued_intermediates)
        {
            Ok(()) => {
                let next_intermediates =
                    if candidate.tbs_certificate.subject != candidate.tbs_certificate.issuer {
                        non_self_issued_intermediates + 1
                    } else {
                        non_self_issued_intermediates
                    };
                visited.push(candidate);
                match verify_certificate_chain_recursive(
                    candidate,
                    token_certs,
                    tsa_root_certs,
                    validation_time,
                    next_intermediates,
                    visited,
                    remaining_verifications,
                ) {
                    Ok(()) => return Ok(()),
                    Err(err) => {
                        visited.pop();
                        record_branch_err(&mut verified_branch_err, err);
                    }
                }
            }
            Err(err) => record_direct_err(&mut candidate_err, err),
        }
    }

    let err = match (verified_branch_err, root_err) {
        (Some(branch_err), _)
            if !matches!(branch_err, TimeStampTokenError::UntrustedCertificateChain) =>
        {
            branch_err
        }
        (_, Some(r_err)) if !matches!(r_err, TimeStampTokenError::SignatureVerification(_)) => {
            r_err
        }
        (Some(branch_err), _) => branch_err,
        (None, Some(r_err)) => r_err,
        (None, None) => candidate_err.unwrap_or(TimeStampTokenError::UntrustedCertificateChain),
    };
    Err(err)
}

/// Verifies that `issuer` signed `subject`, is valid at `validation_time`, and
/// satisfies CA constraints for `intermediates_below`.
fn verify_issuer(
    subject: &Certificate,
    issuer: &Certificate,
    validation_time: Instant,
    intermediates_below: usize,
) -> Result<(), TimeStampTokenError> {
    verify_certificate_signature(subject, issuer)?;
    verify_cert_validity_contains(issuer, validation_time)?;
    verify_ca_constraints(issuer, intermediates_below)
}

/// Verifies that `cert`'s validity period (`not_before..=not_after`) contains
/// `instant` per RFC 5280 Section 4.1.2.5
/// (<https://www.rfc-editor.org/rfc/rfc5280#section-4.1.2.5>).
fn verify_cert_validity_contains(
    cert: &Certificate,
    instant: Instant,
) -> Result<(), TimeStampTokenError> {
    let validity = &cert.tbs_certificate.validity;
    let not_before =
        Instant::from_unix_nanos(validity.not_before.to_unix_duration().as_nanos() as i128);
    let not_after =
        Instant::from_unix_nanos(validity.not_after.to_unix_duration().as_nanos() as i128);

    if instant < not_before || instant > not_after {
        return Err(TimeStampTokenError::CertificateValidityPeriod);
    }
    Ok(())
}

/// Verifies version and CA extensions (`BasicConstraints`, `KeyUsage`,
/// `ExtendedKeyUsage`, and critical extensions) on a CA certificate per:
/// - RFC 5280 Section 4.2 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2>)
/// - RFC 5280 Section 4.2.1.3 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.3>)
/// - RFC 5280 Section 4.2.1.9 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.9>)
/// - RFC 5280 Section 4.2.1.12 (<https://www.rfc-editor.org/rfc/rfc5280#section-4.2.1.12>)
/// - RFC 5280 Section 6.1.4(k)-(o) (<https://www.rfc-editor.org/rfc/rfc5280#section-6.1.4>)
fn verify_ca_constraints(
    ca_cert: &Certificate,
    intermediates_below: usize,
) -> Result<(), TimeStampTokenError> {
    verify_v3_and_critical_extensions(
        ca_cert,
        &[ID_CE_BASIC_CONSTRAINTS, ID_CE_KEY_USAGE, ID_CE_EXT_KEY_USAGE],
    )?;

    let Some((_critical, basic_constraints)) = ca_cert.tbs_certificate.get::<BasicConstraints>()?
    else {
        return Err(TimeStampTokenError::MissingCaBasicConstraints);
    };

    if !basic_constraints.ca {
        return Err(TimeStampTokenError::MissingCaBasicConstraints);
    }
    if let Some(max_len) = basic_constraints.path_len_constraint
        && intermediates_below > usize::from(max_len)
    {
        return Err(TimeStampTokenError::PathLenConstraintExceeded);
    }

    if let Some((_critical, key_usage)) = ca_cert.tbs_certificate.get::<KeyUsage>()?
        && !key_usage.key_cert_sign()
    {
        return Err(TimeStampTokenError::MissingKeyCertSignKeyUsage);
    }

    if let Some((_critical, ExtendedKeyUsage(oids))) =
        ca_cert.tbs_certificate.get::<ExtendedKeyUsage>()?
        && !oids.contains(&ID_KP_TIME_STAMPING)
        && !oids.contains(&ANY_EXTENDED_KEY_USAGE)
    {
        return Err(TimeStampTokenError::InvalidCaExtendedKeyUsage);
    }

    Ok(())
}
