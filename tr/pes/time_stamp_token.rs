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
//! `verify_time_stamp_token` (introduced in the follow-up verification commit)
//! can hash the exact `TSTInfo` DER octets before decoding them.
//!
//! Authoritative specifications:
//! - RFC 3161 (Time-Stamp Protocol): <https://www.rfc-editor.org/rfc/rfc3161>
//! - RFC 5816 (ESSCertIDv2 Update for RFC 3161): <https://www.rfc-editor.org/rfc/rfc5816>
//! - RFC 5035 (ESS Update: Adding CertID Algorithm Agility): <https://www.rfc-editor.org/rfc/rfc5035>
//! - RFC 5652 (Cryptographic Message Syntax): <https://www.rfc-editor.org/rfc/rfc5652>
//! - RFC 5280 (Internet X.509 PKI Certificate and CRL Profile): <https://www.rfc-editor.org/rfc/rfc5280>
//! - RFC 3279 (Algorithms and Identifiers for X.509 PKI): <https://www.rfc-editor.org/rfc/rfc3279>
//! - RFC 4055 (Additional Algorithms and Identifiers for RSA PKCS #1): <https://www.rfc-editor.org/rfc/rfc4055>
//! - RFC 5754 (Using SHA2 Algorithms with CMS): <https://www.rfc-editor.org/rfc/rfc5754>
//! - RFC 5758 (X.509 PKI Validation for DSA and ECDSA): <https://www.rfc-editor.org/rfc/rfc5758>

// Verification helpers in this module are wired into `tests` and `lib` in
// follow-up commits in this stack, where this attribute is removed.
#![allow(dead_code)]

use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

use chrono::{DateTime, Datelike, NaiveDateTime, Timelike, Utc};
use const_oid::{
    ObjectIdentifier,
    db::rfc5912::{
        ECDSA_WITH_SHA_256, ECDSA_WITH_SHA_384, ECDSA_WITH_SHA_512, ID_EC_PUBLIC_KEY, ID_SHA_256,
        ID_SHA_384, ID_SHA_512, RSA_ENCRYPTION, SECP_256_R_1, SHA_256_WITH_RSA_ENCRYPTION,
        SHA_384_WITH_RSA_ENCRYPTION, SHA_512_WITH_RSA_ENCRYPTION,
    },
};
use ecdsa::signature::hazmat::PrehashVerifier as _;
use oak_digest::{Digest, Sha256, Sha384, Sha512};
use oak_time::Instant;
use rsa::{Pkcs1v15Sign, RsaPublicKey, traits::PublicKeyParts as _};
use x509_cert::{
    Certificate,
    attr::Attributes,
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
            certpolicy::PolicyInformation,
            name::{GeneralName, GeneralNames},
        },
    },
    name::Name,
    serial_number::SerialNumber,
    spki::{AlgorithmIdentifierOwned, SubjectPublicKeyInfoOwned},
};

/// PKCS#9 `id-ct-TSTInfo` (`1.2.840.113549.1.9.16.1.4`), RFC 3161 Section
/// 2.4.2.
pub(crate) const ID_CT_TST_INFO: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.16.1.4");

/// S/MIME `id-aa-signingCertificateV2` (`1.2.840.113549.1.9.16.2.47`), RFC 5816
/// Section 2.2 (updating RFC 3161 Section 2.4.2) and RFC 5035 Section 3.
pub(crate) const ID_AA_SIGNING_CERTIFICATE_V2: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.16.2.47");

/// CMS `id-aa-CMSAlgorithmProtection` (`1.2.840.113549.1.9.52`), RFC 6211
/// Section 2.
#[cfg(test)]
pub(crate) const ID_AA_CMS_ALGORITHM_PROTECTION: ObjectIdentifier =
    ObjectIdentifier::new_unwrap("1.2.840.113549.1.9.52");

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

    #[error("missing message-digest attribute in signedAttrs")]
    MissingMessageDigestAttr,

    #[error("signedAttrs message-digest does not match TSTInfo digest")]
    MessageDigestMismatch,

    #[error("missing or invalid signing-certificate attribute in signedAttrs")]
    InvalidSigningCertificateAttr,

    #[error("signing-certificate certHash in signedAttrs does not match TSA signer certificate")]
    SigningCertificateMismatch,

    #[error("messageImprint digest in TSTInfo does not match PES signature digest")]
    MessageImprintMismatch,

    #[error("unsupported digest algorithm {0}")]
    UnsupportedDigestAlgorithm(ObjectIdentifier),

    #[error("invalid parameters for digest algorithm {0}, expected absent or NULL")]
    InvalidDigestAlgorithmParameters(ObjectIdentifier),

    #[error("unsupported signature algorithm {0}")]
    UnsupportedSignatureAlgorithm(ObjectIdentifier),

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
#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CmsAlgorithmProtection {
    pub digest_algorithm: AlgorithmIdentifierOwned,
    pub signature_algorithm: Option<AlgorithmIdentifierOwned>,
    pub mac_algorithm: Option<AlgorithmIdentifierOwned>,
}

#[cfg(test)]
impl FixedTag for CmsAlgorithmProtection {
    const TAG: Tag = Tag::Sequence;
}

#[cfg(test)]
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

#[cfg(test)]
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
        if let Some(ref params) = alg.parameters
            && !params.is_null()
        {
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

/// Resolves a CMS `(digestAlgorithm, signatureAlgorithm)` pair into a combined
/// X.509 signature `AlgorithmIdentifierOwned` per RFC 5652 Section 5.3
/// (<https://www.rfc-editor.org/rfc/rfc5652#section-5.3>).
fn resolve_cms_signature_algorithm(
    digest_alg_id: &AlgorithmIdentifierOwned,
    sig_alg: &AlgorithmIdentifierOwned,
) -> Result<AlgorithmIdentifierOwned, TimeStampTokenError> {
    let digest_alg = DigestAlgorithm::from_algorithm(digest_alg_id)?;
    let sig_oid = sig_alg.oid;

    match sig_oid {
        RSA_ENCRYPTION => {
            let resolved_oid = match digest_alg {
                DigestAlgorithm::Sha256 => SHA_256_WITH_RSA_ENCRYPTION,
                DigestAlgorithm::Sha384 => SHA_384_WITH_RSA_ENCRYPTION,
                DigestAlgorithm::Sha512 => SHA_512_WITH_RSA_ENCRYPTION,
            };
            Ok(AlgorithmIdentifierOwned {
                oid: resolved_oid,
                parameters: sig_alg.parameters.clone(),
            })
        }
        ID_EC_PUBLIC_KEY => {
            if let Some(ref params) = sig_alg.parameters
                && !params.is_null()
            {
                return Err(TimeStampTokenError::SignatureVerification(
                    "invalid ECDSA CMS signature algorithm parameters".to_string(),
                ));
            }
            let resolved_oid = match digest_alg {
                DigestAlgorithm::Sha256 => ECDSA_WITH_SHA_256,
                DigestAlgorithm::Sha384 => ECDSA_WITH_SHA_384,
                DigestAlgorithm::Sha512 => ECDSA_WITH_SHA_512,
            };
            Ok(AlgorithmIdentifierOwned { oid: resolved_oid, parameters: None })
        }
        _ => {
            let expected_digest = match sig_oid {
                SHA_256_WITH_RSA_ENCRYPTION | ECDSA_WITH_SHA_256 => DigestAlgorithm::Sha256,
                SHA_384_WITH_RSA_ENCRYPTION | ECDSA_WITH_SHA_384 => DigestAlgorithm::Sha384,
                SHA_512_WITH_RSA_ENCRYPTION | ECDSA_WITH_SHA_512 => DigestAlgorithm::Sha512,
                _ => return Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(sig_oid)),
            };

            if expected_digest != digest_alg {
                return Err(TimeStampTokenError::IncompatibleDigestAndSignatureAlgorithms {
                    digest_alg: digest_alg_id.oid,
                    sig_alg: sig_oid,
                });
            }

            Ok(AlgorithmIdentifierOwned { oid: sig_oid, parameters: sig_alg.parameters.clone() })
        }
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
    sig_alg: &AlgorithmIdentifierOwned,
    message: &[u8],
    signature_bytes: &[u8],
) -> Result<(), TimeStampTokenError> {
    let sig_oid = sig_alg.oid;
    let spki_ref = spki.owned_to_ref();

    match sig_oid {
        SHA_256_WITH_RSA_ENCRYPTION | SHA_384_WITH_RSA_ENCRYPTION | SHA_512_WITH_RSA_ENCRYPTION => {
            if let Some(ref params) = sig_alg.parameters
                && !params.is_null()
            {
                return Err(TimeStampTokenError::SignatureVerification(
                    "invalid RSA signature algorithm parameters".to_string(),
                ));
            }
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
            let verify_res = match sig_oid {
                SHA_256_WITH_RSA_ENCRYPTION => rsa_key.verify(
                    Pkcs1v15Sign::new::<sha2::Sha256>(),
                    Sha256::from_contents(message).as_ref(),
                    signature_bytes,
                ),
                SHA_384_WITH_RSA_ENCRYPTION => rsa_key.verify(
                    Pkcs1v15Sign::new::<sha2::Sha384>(),
                    Sha384::from_contents(message).as_ref(),
                    signature_bytes,
                ),
                _ => rsa_key.verify(
                    Pkcs1v15Sign::new::<sha2::Sha512>(),
                    Sha512::from_contents(message).as_ref(),
                    signature_bytes,
                ),
            };
            verify_res.map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))
        }
        ECDSA_WITH_SHA_256 | ECDSA_WITH_SHA_384 | ECDSA_WITH_SHA_512 => {
            if sig_alg.parameters.is_some() {
                return Err(TimeStampTokenError::SignatureVerification(
                    "unexpected parameters in ECDSA signature algorithm".to_string(),
                ));
            }
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
            let digest = match sig_oid {
                ECDSA_WITH_SHA_256 => DigestAlgorithm::Sha256.digest(message),
                ECDSA_WITH_SHA_384 => DigestAlgorithm::Sha384.digest(message),
                _ => DigestAlgorithm::Sha512.digest(message),
            };
            // `ecdsa::VerifyingKey::verify_prehash` converts `digest` to a field
            // element via `ecdsa::hazmat::bits2field` per RFC 6979 Section 2.3.2
            // (<https://www.rfc-editor.org/rfc/rfc6979#section-2.3.2>), truncating
            // digests wider than the curve's field (e.g. SHA-384 or SHA-512 with
            // P-256).
            //
            // Note: P-384 (`secp384r1`) is intentionally omitted for now to avoid
            // adding a `p384` crate dependency to `pes`.
            match curve_oid {
                SECP_256_R_1 => {
                    let vk = p256::ecdsa::VerifyingKey::try_from(spki_ref)
                        .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))?;
                    let sig = p256::ecdsa::Signature::from_der(signature_bytes)
                        .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))?;
                    vk.verify_prehash(digest.as_ref(), &sig)
                        .map_err(|e| TimeStampTokenError::SignatureVerification(format!("{e}")))
                }
                _ => Err(TimeStampTokenError::SignatureVerification(format!(
                    "unsupported EC curve {curve_oid}"
                ))),
            }
        }
        _ => Err(TimeStampTokenError::UnsupportedSignatureAlgorithm(sig_oid)),
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
    if subject.signature.unused_bits() != 0 {
        return Err(TimeStampTokenError::SignatureVerification(
            "certificate signature BIT STRING has non-zero unused bits".to_string(),
        ));
    }
    let tbs_der = subject.tbs_certificate.to_der()?;
    verify_spki_signature(
        &issuer.tbs_certificate.subject_public_key_info,
        &subject.signature_algorithm,
        &tbs_der,
        subject.signature.raw_bytes(),
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
