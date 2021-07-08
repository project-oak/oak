use crate::ber::{bitstring_to_u64, bytes_to_u64};
use crate::error::BerError;
use crate::oid::Oid;
use nom::bitvec::{order::Msb0, slice::BitSlice};
use rusticata_macros::newtype_enum;
use std::convert::AsRef;
use std::convert::From;
use std::convert::TryFrom;
use std::fmt;
use std::ops::Index;
use std::vec::Vec;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BerClassFromIntError(pub(crate) ());

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BerSizeError(pub(crate) ());

/// BER Object class of tag
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum BerClass {
    Universal = 0b00,
    Application = 0b01,
    ContextSpecific = 0b10,
    Private = 0b11,
}

/// Ber Object Length
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BerSize {
    /// Definite form (X.690 8.1.3.3)
    Definite(usize),
    /// Indefinite form (X.690 8.1.3.6)
    Indefinite,
}

/// BER/DER Tag as defined in X.680 section 8.4
///
/// X.690 doesn't specify the maximum tag size so we're assuming that people
/// aren't going to need anything more than a u32.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BerTag(pub u32);

newtype_enum! {
impl debug BerTag {
    EndOfContent = 0x0,
    Boolean = 0x1,
    Integer = 0x2,
    BitString = 0x3,
    OctetString = 0x4,
    Null = 0x05,
    Oid = 0x06,
    ObjDescriptor = 0x07,
    External = 0x08,
    RealType = 0x09,
    Enumerated = 0xa,
    EmbeddedPdv = 0xb,
    Utf8String = 0xc,
    RelativeOid = 0xd,

    Sequence = 0x10,
    Set = 0x11,
    NumericString = 0x12,
    PrintableString = 0x13,
    T61String = 0x14,
    VideotexString = 0x15,

    Ia5String = 0x16,
    UtcTime = 0x17,
    GeneralizedTime = 0x18,

    GraphicString = 25, // 0x19
    VisibleString = 26, // 0x1a
    GeneralString = 27, // 0x1b

    UniversalString = 0x1c,
    BmpString = 0x1e,

    Invalid = 0xff,
}
}

/// Representation of a BER-encoded (X.690) object
///
/// A BER object is composed of a header describing the object class, type and length,
/// and the content.
///
/// Note that the content may sometimes not match the header tag (for ex when parsing IMPLICIT
/// tagged values).
#[derive(Debug, Clone, PartialEq)]
pub struct BerObject<'a> {
    pub header: BerObjectHeader<'a>,
    pub content: BerObjectContent<'a>,
}

/// BER object header (identifier and length)
#[derive(Clone, Debug)]
pub struct BerObjectHeader<'a> {
    /// Object class: universal, application, context-specific, or private
    pub class: BerClass,
    /// Constructed attribute: 1 if constructed, else 0
    pub structured: u8,
    /// Tag number
    pub tag: BerTag,
    /// Object length: definite or indefinite
    pub len: BerSize,

    /// Optionally, the raw encoding of the tag
    ///
    /// This is useful in some cases, where different representations of the same
    /// BER tags have different meanings (BER only)
    pub raw_tag: Option<&'a [u8]>,
}

/// BER object content
#[derive(Debug, Clone, PartialEq)]
pub enum BerObjectContent<'a> {
    /// EOC (no content)
    EndOfContent,
    /// BOOLEAN: decoded value
    Boolean(bool),
    /// INTEGER: raw bytes
    ///
    /// Note: the reason to store the raw bytes is that integers have non-finite length in the
    /// spec, and also that the raw encoding is also important for some applications.
    ///
    /// To extract the number, see the `as_u64`, `as_u32`, `as_bigint` and `as_biguint` methods.
    Integer(&'a [u8]),
    /// BIT STRING: number of unused bits, and object
    BitString(u8, BitStringObject<'a>),
    /// OCTET STRING: slice
    OctetString(&'a [u8]),
    /// NULL (no content)
    Null,
    /// ENUMERATED: decoded enum number
    Enum(u64),
    /// OID
    OID(Oid<'a>),
    /// RELATIVE OID
    RelativeOID(Oid<'a>),
    /// NumericString: decoded string
    NumericString(&'a str),
    /// VisibleString: decoded string
    VisibleString(&'a str),
    /// PrintableString: decoded string
    PrintableString(&'a str),
    /// IA5String: decoded string
    IA5String(&'a str),
    /// UTF8String: decoded string
    UTF8String(&'a str),
    /// T61String: raw object bytes
    T61String(&'a [u8]),
    /// VideotexString: raw object bytes
    VideotexString(&'a [u8]),

    /// BmpString: raw object bytes
    BmpString(&'a [u8]),
    /// UniversalString: raw object bytes
    UniversalString(&'a [u8]),

    /// SEQUENCE: list of objects
    Sequence(Vec<BerObject<'a>>),
    /// SET: list of objects
    Set(Vec<BerObject<'a>>),

    /// UTCTime: decoded string
    UTCTime(&'a str),
    /// GeneralizedTime: decoded string
    GeneralizedTime(&'a str),

    /// Object descriptor: raw object bytes
    ObjectDescriptor(&'a [u8]),
    /// GraphicString: raw object bytes
    GraphicString(&'a [u8]),
    /// GeneralString: raw object bytes
    GeneralString(&'a [u8]),

    /// Optional object
    Optional(Option<Box<BerObject<'a>>>),
    /// Tagged object (EXPLICIT): class, tag  and content of inner object
    Tagged(BerClass, BerTag, Box<BerObject<'a>>),

    /// Unknown object: object tag (copied from header), and raw content
    Unknown(BerTag, &'a [u8]),
}

impl fmt::Display for BerClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BerClass::Universal => "UNIVERSAL",
            BerClass::Application => "APPLICATION",
            BerClass::ContextSpecific => "CONTEXT-SPECIFIC",
            BerClass::Private => "PRIVATE",
        };
        write!(f, "{}", s)
    }
}

impl From<u32> for BerTag {
    fn from(v: u32) -> Self {
        BerTag(v)
    }
}

impl BerSize {
    /// Return true if length is definite and equal to 0
    pub fn is_null(&self) -> bool {
        *self == BerSize::Definite(0)
    }

    /// Get length of primitive object
    #[inline]
    pub fn primitive(&self) -> Result<usize, BerError> {
        match self {
            BerSize::Definite(sz) => Ok(*sz),
            BerSize::Indefinite => Err(BerError::IndefiniteLengthUnexpected),
        }
    }
}

impl From<usize> for BerSize {
    fn from(v: usize) -> Self {
        BerSize::Definite(v)
    }
}

impl TryFrom<u64> for BerSize {
    type Error = BerSizeError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let v = usize::try_from(value).or(Err(BerSizeError(())))?;
        Ok(BerSize::Definite(v))
    }
}

impl TryFrom<BerSize> for usize {
    type Error = BerSizeError;

    #[inline]
    fn try_from(value: BerSize) -> Result<Self, Self::Error> {
        match value {
            BerSize::Definite(sz) => Ok(sz),
            BerSize::Indefinite => Err(BerSizeError(())),
        }
    }
}

impl TryFrom<u8> for BerClass {
    type Error = BerClassFromIntError;

    #[inline]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0b00 => Ok(BerClass::Universal),
            0b01 => Ok(BerClass::Application),
            0b10 => Ok(BerClass::ContextSpecific),
            0b11 => Ok(BerClass::Private),
            _ => Err(BerClassFromIntError(())),
        }
    }
}

impl<'a> BerObjectHeader<'a> {
    /// Build a new BER header
    pub fn new<Len: Into<BerSize>>(class: BerClass, structured: u8, tag: BerTag, len: Len) -> Self {
        BerObjectHeader {
            tag,
            structured,
            class,
            len: len.into(),
            raw_tag: None,
        }
    }

    /// Update header class
    #[inline]
    pub fn with_class(self, class: BerClass) -> Self {
        BerObjectHeader { class, ..self }
    }

    /// Update header tag
    #[inline]
    pub fn with_tag(self, tag: BerTag) -> Self {
        BerObjectHeader { tag, ..self }
    }

    /// Update header length
    #[inline]
    pub fn with_len(self, len: BerSize) -> Self {
        BerObjectHeader { len, ..self }
    }

    /// Update header to add reference to raw tag
    #[inline]
    pub fn with_raw_tag(self, raw_tag: Option<&'a [u8]>) -> Self {
        BerObjectHeader { raw_tag, ..self }
    }

    /// Test if object class is Universal
    #[inline]
    pub fn is_universal(&self) -> bool {
        self.class == BerClass::Universal
    }
    /// Test if object class is Application
    #[inline]
    pub fn is_application(&self) -> bool {
        self.class == BerClass::Application
    }
    /// Test if object class is Context-specific
    #[inline]
    pub fn is_contextspecific(&self) -> bool {
        self.class == BerClass::ContextSpecific
    }
    /// Test if object class is Private
    #[inline]
    pub fn is_private(&self) -> bool {
        self.class == BerClass::Private
    }

    /// Test if object is primitive
    #[inline]
    pub fn is_primitive(&self) -> bool {
        self.structured == 0
    }
    /// Test if object is constructed
    #[inline]
    pub fn is_constructed(&self) -> bool {
        self.structured == 1
    }
}

impl<'a> BerObject<'a> {
    /// Build a BerObject from a header and content.
    ///
    /// Note: values are not checked, so the tag can be different from the real content, or flags
    /// can be invalid.
    pub fn from_header_and_content<'o>(
        header: BerObjectHeader<'o>,
        content: BerObjectContent<'o>,
    ) -> BerObject<'o> {
        BerObject { header, content }
    }

    /// Build a BerObject from its content, using default flags (no class, correct tag,
    /// and structured flag set only for Set and Sequence)
    pub fn from_obj(c: BerObjectContent) -> BerObject {
        let class = BerClass::Universal;
        let tag = c.tag();
        let structured = match tag {
            BerTag::Sequence | BerTag::Set => 1,
            _ => 0,
        };
        let header = BerObjectHeader::new(class, structured, tag, BerSize::Definite(0));
        BerObject { header, content: c }
    }

    /// Build a DER integer object from a slice containing an encoded integer
    pub fn from_int_slice(i: &'a [u8]) -> BerObject<'a> {
        let header = BerObjectHeader::new(
            BerClass::Universal,
            0,
            BerTag::Integer,
            BerSize::Definite(0),
        );
        BerObject {
            header,
            content: BerObjectContent::Integer(i),
        }
    }

    /// Set a tag for the BER object
    pub fn set_raw_tag(self, raw_tag: Option<&'a [u8]>) -> BerObject {
        let header = BerObjectHeader {
            raw_tag,
            ..self.header
        };
        BerObject { header, ..self }
    }

    /// Build a DER sequence object from a vector of DER objects
    pub fn from_seq(l: Vec<BerObject>) -> BerObject {
        BerObject::from_obj(BerObjectContent::Sequence(l))
    }

    /// Build a DER set object from a vector of DER objects
    pub fn from_set(l: Vec<BerObject>) -> BerObject {
        BerObject::from_obj(BerObjectContent::Set(l))
    }

    /// Build a BER header from this object content
    #[deprecated(
        since = "0.5.0",
        note = "please use `obj.header` or `obj.header.clone()` instead"
    )]
    pub fn to_header(&self) -> BerObjectHeader {
        self.header.clone()
    }

    /// Attempt to read integer value from DER object.
    /// This can fail if the object is not an integer, or if it is too large.
    ///
    /// ```rust
    /// # use der_parser::ber::BerObject;
    /// let der_int  = BerObject::from_int_slice(b"\x01\x00\x01");
    /// assert_eq!(
    ///     der_int.as_u64(),
    ///     Ok(0x10001)
    /// );
    /// ```
    pub fn as_u64(&self) -> Result<u64, BerError> {
        self.content.as_u64()
    }

    /// Attempt to read integer value from DER object.
    /// This can fail if the object is not an integer, or if it is too large.
    ///
    /// ```rust
    /// # extern crate der_parser;
    /// # use der_parser::ber::{BerObject,BerObjectContent};
    /// let der_int  = BerObject::from_obj(BerObjectContent::Integer(b"\x01\x00\x01"));
    /// assert_eq!(
    ///     der_int.as_u32(),
    ///     Ok(0x10001)
    /// );
    /// ```
    pub fn as_u32(&self) -> Result<u32, BerError> {
        self.content.as_u32()
    }

    /// Attempt to read integer value from DER object.
    /// This can fail if the object is not a boolean.
    pub fn as_bool(&self) -> Result<bool, BerError> {
        self.content.as_bool()
    }

    /// Attempt to read an OID value from DER object.
    /// This can fail if the object is not an OID.
    pub fn as_oid(&self) -> Result<&Oid<'a>, BerError> {
        self.content.as_oid()
    }

    /// Attempt to read an OID value from DER object.
    /// This can fail if the object is not an OID.
    pub fn as_oid_val(&self) -> Result<Oid<'a>, BerError> {
        self.content.as_oid_val()
    }

    /// Attempt to get a reference on the content from an optional object.
    /// This can fail if the object is not optional.
    pub fn as_optional(&'a self) -> Result<Option<&'_ BerObject<'a>>, BerError> {
        self.content.as_optional()
    }

    /// Attempt to get a reference on the content from a tagged object.
    /// This can fail if the object is not tagged.
    pub fn as_tagged(&'a self) -> Result<(BerClass, BerTag, &'_ BerObject<'a>), BerError> {
        self.content.as_tagged()
    }

    /// Attempt to read a reference to a BitString value from DER object.
    /// This can fail if the object is not an BitString.
    ///
    /// Note that this function returns a reference to the BitString. To get an owned value,
    /// use [`as_bitstring`](struct.BerObject.html#method.as_bitstring)
    pub fn as_bitstring_ref(&self) -> Result<&BitStringObject, BerError> {
        self.content.as_bitstring_ref()
    }

    /// Attempt to read a BitString value from DER object.
    /// This can fail if the object is not an BitString.
    pub fn as_bitstring(&'a self) -> Result<BitStringObject<'a>, BerError> {
        self.content.as_bitstring()
    }

    /// Constructs a shared `&BitSlice` reference over the object data, if available as slice.
    pub fn as_bitslice(&self) -> Result<&BitSlice<Msb0, u8>, BerError> {
        self.content.as_bitslice()
    }

    /// Attempt to extract the list of objects from a DER sequence.
    /// This can fail if the object is not a sequence.
    pub fn as_sequence(&self) -> Result<&Vec<BerObject<'a>>, BerError> {
        self.content.as_sequence()
    }

    /// Attempt to extract the list of objects from a DER set.
    /// This can fail if the object is not a set.
    pub fn as_set(&self) -> Result<&Vec<BerObject<'a>>, BerError> {
        self.content.as_set()
    }

    /// Attempt to get the content from a DER object, as a slice.
    /// This can fail if the object does not contain a type directly equivalent to a slice (e.g a
    /// sequence).
    /// This function mostly concerns string types, integers, or unknown DER objects.
    pub fn as_slice(&self) -> Result<&'a [u8], BerError> {
        self.content.as_slice()
    }

    /// Attempt to get the content from a DER object, as a str.
    /// This can fail if the object does not contain a string type.
    ///
    /// Only NumericString, VisibleString, UTCTime, GeneralizedTime,
    /// PrintableString, UTF8String and IA5String are considered here. Other
    /// string types can be read using `as_slice`.
    pub fn as_str(&self) -> Result<&'a str, BerError> {
        self.content.as_str()
    }

    /// Test if object class is Universal
    pub fn is_universal(&self) -> bool {
        self.header.class == BerClass::Universal
    }
    /// Test if object class is Application
    pub fn is_application(&self) -> bool {
        self.header.class == BerClass::Application
    }
    /// Test if object class is Context-specific
    pub fn is_contextspecific(&self) -> bool {
        self.header.class == BerClass::ContextSpecific
    }
    /// Test if object class is Private
    pub fn is_private(&self) -> bool {
        self.header.class == BerClass::Private
    }

    /// Test if object is primitive
    pub fn is_primitive(&self) -> bool {
        self.header.structured == 0
    }
    /// Test if object is constructed
    pub fn is_constructed(&self) -> bool {
        self.header.structured == 1
    }
}

/// Build a DER object from an OID.
impl<'a> From<Oid<'a>> for BerObject<'a> {
    fn from(oid: Oid<'a>) -> BerObject<'a> {
        BerObject::from_obj(BerObjectContent::OID(oid))
    }
}

/// Build a DER object from a BerObjectContent.
impl<'a> From<BerObjectContent<'a>> for BerObject<'a> {
    fn from(obj: BerObjectContent<'a>) -> BerObject<'a> {
        BerObject::from_obj(obj)
    }
}

/// Replacement function for Option.xor (>= 1.37)
#[inline]
pub(crate) fn xor_option<T>(opta: Option<T>, optb: Option<T>) -> Option<T> {
    match (opta, optb) {
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        _ => None,
    }
}

/// Compare two BER headers. `len` fields are compared only if both objects have it set (same for `raw_tag`)
impl<'a> PartialEq<BerObjectHeader<'a>> for BerObjectHeader<'a> {
    fn eq(&self, other: &BerObjectHeader) -> bool {
        self.class == other.class
            && self.tag == other.tag
            && self.structured == other.structured
            && {
                if self.len.is_null() && other.len.is_null() {
                    self.len == other.len
                } else {
                    true
                }
            }
            && {
                // it tag is present for both, compare it
                if xor_option(self.raw_tag, other.raw_tag).is_none() {
                    self.raw_tag == other.raw_tag
                } else {
                    true
                }
            }
    }
}

impl<'a> BerObjectContent<'a> {
    pub fn as_u64(&self) -> Result<u64, BerError> {
        match self {
            BerObjectContent::Integer(i) => bytes_to_u64(i),
            BerObjectContent::BitString(ignored_bits, data) => {
                bitstring_to_u64(*ignored_bits as usize, data)
            }
            BerObjectContent::Enum(i) => Ok(*i as u64),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_u32(&self) -> Result<u32, BerError> {
        match self {
            BerObjectContent::Integer(i) => bytes_to_u64(i).and_then(|x| {
                if x > u64::from(std::u32::MAX) {
                    Err(BerError::IntegerTooLarge)
                } else {
                    Ok(x as u32)
                }
            }),
            BerObjectContent::BitString(ignored_bits, data) => {
                bitstring_to_u64(*ignored_bits as usize, data).and_then(|x| {
                    if x > u64::from(std::u32::MAX) {
                        Err(BerError::IntegerTooLarge)
                    } else {
                        Ok(x as u32)
                    }
                })
            }
            BerObjectContent::Enum(i) => {
                if *i > u64::from(std::u32::MAX) {
                    Err(BerError::IntegerTooLarge)
                } else {
                    Ok(*i as u32)
                }
            }
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_bool(&self) -> Result<bool, BerError> {
        match *self {
            BerObjectContent::Boolean(b) => Ok(b),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_oid(&self) -> Result<&Oid<'a>, BerError> {
        match *self {
            BerObjectContent::OID(ref o) => Ok(o),
            BerObjectContent::RelativeOID(ref o) => Ok(o),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_oid_val(&self) -> Result<Oid<'a>, BerError> {
        self.as_oid().map(|o| o.clone())
    }

    pub fn as_optional(&'a self) -> Result<Option<&'_ BerObject<'a>>, BerError> {
        match *self {
            BerObjectContent::Optional(Some(ref o)) => Ok(Some(&o)),
            BerObjectContent::Optional(None) => Ok(None),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_tagged(&'a self) -> Result<(BerClass, BerTag, &'_ BerObject<'a>), BerError> {
        match *self {
            BerObjectContent::Tagged(class, tag, ref o) => Ok((class, tag, o.as_ref())),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_bitstring_ref(&self) -> Result<&BitStringObject, BerError> {
        match *self {
            BerObjectContent::BitString(_, ref b) => Ok(b),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_bitstring(&'a self) -> Result<BitStringObject<'a>, BerError> {
        match *self {
            BerObjectContent::BitString(_, ref b) => Ok(b.to_owned()),
            _ => Err(BerError::BerTypeError),
        }
    }

    /// Constructs a shared `&BitSlice` reference over the object data, if available as slice.
    pub fn as_bitslice(&self) -> Result<&BitSlice<Msb0, u8>, BerError> {
        self.as_slice()
            .and_then(|s| BitSlice::<Msb0, _>::from_slice(s).ok_or(BerError::BerValueError))
    }

    pub fn as_sequence(&self) -> Result<&Vec<BerObject<'a>>, BerError> {
        match *self {
            BerObjectContent::Sequence(ref s) => Ok(s),
            _ => Err(BerError::BerTypeError),
        }
    }

    pub fn as_set(&self) -> Result<&Vec<BerObject<'a>>, BerError> {
        match *self {
            BerObjectContent::Set(ref s) => Ok(s),
            _ => Err(BerError::BerTypeError),
        }
    }

    #[rustfmt::skip]
    pub fn as_slice(&self) -> Result<&'a [u8],BerError> {
        match *self {
            BerObjectContent::NumericString(s) |
            BerObjectContent::GeneralizedTime(s) |
            BerObjectContent::UTCTime(s) |
            BerObjectContent::VisibleString(s) |
            BerObjectContent::PrintableString(s) |
            BerObjectContent::UTF8String(s) |
            BerObjectContent::IA5String(s) => Ok(s.as_ref()),
            BerObjectContent::Integer(s) |
            BerObjectContent::BitString(_,BitStringObject{data:s}) |
            BerObjectContent::OctetString(s) |
            BerObjectContent::T61String(s) |
            BerObjectContent::VideotexString(s) |
            BerObjectContent::BmpString(s) |
            BerObjectContent::UniversalString(s) |
            BerObjectContent::ObjectDescriptor(s) |
            BerObjectContent::GraphicString(s) |
            BerObjectContent::GeneralString(s) |
            BerObjectContent::Unknown(_,s) => Ok(s),
            _ => Err(BerError::BerTypeError),
        }
    }

    #[rustfmt::skip]
    pub fn as_str(&self) -> Result<&'a str,BerError> {
        match *self {
            BerObjectContent::NumericString(s) |
            BerObjectContent::GeneralizedTime(s) |
            BerObjectContent::UTCTime(s) |
            BerObjectContent::VisibleString(s) |
            BerObjectContent::PrintableString(s) |
            BerObjectContent::UTF8String(s) |
            BerObjectContent::IA5String(s) => Ok(s),
            _ => Err(BerError::BerTypeError),
        }
    }

    #[rustfmt::skip]
    fn tag(&self) -> BerTag {
        match self {
            BerObjectContent::EndOfContent         => BerTag::EndOfContent,
            BerObjectContent::Boolean(_)           => BerTag::Boolean,
            BerObjectContent::Integer(_)           => BerTag::Integer,
            BerObjectContent::BitString(_,_)       => BerTag::BitString,
            BerObjectContent::OctetString(_)       => BerTag::OctetString,
            BerObjectContent::Null                 => BerTag::Null,
            BerObjectContent::Enum(_)              => BerTag::Enumerated,
            BerObjectContent::OID(_)               => BerTag::Oid,
            BerObjectContent::NumericString(_)     => BerTag::NumericString,
            BerObjectContent::VisibleString(_)     => BerTag::VisibleString,
            BerObjectContent::PrintableString(_)   => BerTag::PrintableString,
            BerObjectContent::IA5String(_)         => BerTag::Ia5String,
            BerObjectContent::UTF8String(_)        => BerTag::Utf8String,
            BerObjectContent::RelativeOID(_)       => BerTag::RelativeOid,
            BerObjectContent::T61String(_)         => BerTag::T61String,
            BerObjectContent::VideotexString(_)    => BerTag::VideotexString,
            BerObjectContent::BmpString(_)         => BerTag::BmpString,
            BerObjectContent::UniversalString(_)   => BerTag::UniversalString,
            BerObjectContent::Sequence(_)          => BerTag::Sequence,
            BerObjectContent::Set(_)               => BerTag::Set,
            BerObjectContent::UTCTime(_)           => BerTag::UtcTime,
            BerObjectContent::GeneralizedTime(_)   => BerTag::GeneralizedTime,
            BerObjectContent::ObjectDescriptor(_)  => BerTag::ObjDescriptor,
            BerObjectContent::GraphicString(_)     => BerTag::GraphicString,
            BerObjectContent::GeneralString(_)     => BerTag::GeneralString,
            BerObjectContent::Tagged(_,x,_) |
            BerObjectContent::Unknown(x,_)         => *x,
            BerObjectContent::Optional(Some(obj))  => obj.content.tag(),
            BerObjectContent::Optional(None)       => BerTag(0x00), // XXX invalid !
        }
    }
}

#[cfg(feature = "bigint")]
#[cfg_attr(docsrs, doc(cfg(feature = "bigint")))]
use num_bigint::{BigInt, BigUint, Sign};

#[cfg(feature = "bigint")]
#[cfg_attr(docsrs, doc(cfg(feature = "bigint")))]
impl<'a> BerObject<'a> {
    pub fn as_bigint(&self) -> Option<BigInt> {
        match self.content {
            BerObjectContent::Integer(s) => Some(BigInt::from_bytes_be(Sign::Plus, s)),
            _ => None,
        }
    }

    pub fn as_biguint(&self) -> Option<BigUint> {
        match self.content {
            BerObjectContent::Integer(s) => Some(BigUint::from_bytes_be(s)),
            _ => None,
        }
    }
}

// This is a consuming iterator
impl<'a> IntoIterator for BerObject<'a> {
    type Item = BerObject<'a>;
    type IntoIter = BerObjectIntoIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        // match self {
        //     BerObjectContent::Sequence(ref v) => (),
        //     _ => (),
        // };
        BerObjectIntoIterator { val: self, idx: 0 }
    }
}

#[derive(Debug)]
pub struct BerObjectIntoIterator<'a> {
    val: BerObject<'a>,
    idx: usize,
}

impl<'a> Iterator for BerObjectIntoIterator<'a> {
    type Item = BerObject<'a>;
    fn next(&mut self) -> Option<BerObject<'a>> {
        // let result = if self.idx < self.vec.len() {
        //     Some(self.vec[self.idx].clone())
        // } else {
        //     None
        // };
        let res = match self.val.content {
            BerObjectContent::Sequence(ref v) if self.idx < v.len() => Some(v[self.idx].clone()),
            BerObjectContent::Set(ref v) if self.idx < v.len() => Some(v[self.idx].clone()),
            _ => {
                if self.idx == 0 {
                    Some(self.val.clone())
                } else {
                    None
                }
            }
        };
        self.idx += 1;
        res
    }
}

// impl<'a> Iterator for BerObjectContent<'a> {
//     type Item = BerObjectContent<'a>;
//
//     fn next(&mut self) -> Option<BerObjectContent<'a>> {
//         None
//     }
// }

#[derive(Debug)]
pub struct BerObjectRefIterator<'a> {
    obj: &'a BerObject<'a>,
    idx: usize,
}

impl<'a> Iterator for BerObjectRefIterator<'a> {
    type Item = &'a BerObject<'a>;
    fn next(&mut self) -> Option<&'a BerObject<'a>> {
        let res = match (*self.obj).content {
            BerObjectContent::Sequence(ref v) if self.idx < v.len() => Some(&v[self.idx]),
            BerObjectContent::Set(ref v) if self.idx < v.len() => Some(&v[self.idx]),
            _ => None,
        };
        self.idx += 1;
        res
    }
}

impl<'a> BerObject<'a> {
    pub fn ref_iter(&'a self) -> BerObjectRefIterator<'a> {
        BerObjectRefIterator { obj: self, idx: 0 }
    }
}

impl<'a> Index<usize> for BerObject<'a> {
    type Output = BerObject<'a>;

    fn index(&self, idx: usize) -> &BerObject<'a> {
        match (*self).content {
            BerObjectContent::Sequence(ref v) if idx < v.len() => &v[idx],
            BerObjectContent::Set(ref v) if idx < v.len() => &v[idx],
            _ => panic!("Try to index BerObjectContent which is not structured"),
        }
        // XXX the following
        // self.ref_iter().nth(idx).unwrap()
        // fails with:
        // error: cannot infer an appropriate lifetime for autoref due to conflicting requirements [E0495]
        // self.ref_iter().nth(idx).unwrap()
    }
}

/// BitString wrapper
#[derive(Clone, Debug, PartialEq)]
pub struct BitStringObject<'a> {
    pub data: &'a [u8],
}

impl<'a> BitStringObject<'a> {
    /// Test if bit `bitnum` is set
    pub fn is_set(&self, bitnum: usize) -> bool {
        let byte_pos = bitnum / 8;
        if byte_pos >= self.data.len() {
            return false;
        }
        let b = 7 - (bitnum % 8);
        (self.data[byte_pos] & (1 << b)) != 0
    }

    /// Constructs a shared `&BitSlice` reference over the object data.
    pub fn as_bitslice(&self) -> Option<&BitSlice<Msb0, u8>> {
        BitSlice::<Msb0, _>::from_slice(&self.data)
    }
}

impl<'a> AsRef<[u8]> for BitStringObject<'a> {
    fn as_ref(&self) -> &[u8] {
        self.data
    }
}

#[cfg(test)]
mod tests {
    use crate::ber::*;
    use crate::oid::*;

    #[test]
    fn test_der_as_u64() {
        let der_obj = BerObject::from_int_slice(b"\x01\x00\x02");
        assert_eq!(der_obj.as_u64(), Ok(0x10002));
    }

    #[test]
    fn test_ber_as_u64_bitstring() {
        let (_, ber_obj) = parse_ber_bitstring(b"\x03\x04\x06\x6e\x5d\xc0").unwrap();
        assert_eq!(ber_obj.as_u64(), Ok(0b011011100101110111));

        let (_, ber_obj_with_nonzero_padding) =
            parse_ber_bitstring(b"\x03\x04\x06\x6e\x5d\xe0").unwrap();
        assert_eq!(
            ber_obj_with_nonzero_padding.as_u64(),
            Ok(0b011011100101110111)
        );
    }

    #[test]
    fn test_der_seq_iter() {
        let der_obj = BerObject::from_obj(BerObjectContent::Sequence(vec![
            BerObject::from_int_slice(b"\x01\x00\x01"),
            BerObject::from_int_slice(b"\x01\x00\x00"),
        ]));
        let expected_values = vec![
            BerObject::from_int_slice(b"\x01\x00\x01"),
            BerObject::from_int_slice(b"\x01\x00\x00"),
        ];

        for (idx, v) in der_obj.ref_iter().enumerate() {
            // println!("v: {:?}", v);
            assert_eq!((*v), expected_values[idx]);
        }
    }

    #[test]
    fn test_der_from_oid() {
        let obj: BerObject = Oid::from(&[1, 2]).unwrap().into();
        let expected = BerObject::from_obj(BerObjectContent::OID(Oid::from(&[1, 2]).unwrap()));

        assert_eq!(obj, expected);
    }

    #[test]
    fn test_der_bitstringobject() {
        let obj = BitStringObject {
            data: &[0x0f, 0x00, 0x40],
        };
        assert!(!obj.is_set(0));
        assert!(obj.is_set(7));
        assert!(!obj.is_set(9));
        assert!(obj.is_set(17));
    }

    #[test]
    fn test_der_bitslice() {
        let obj = BitStringObject {
            data: &[0x0f, 0x00, 0x40],
        };
        let slice = obj.as_bitslice().expect("as_bitslice");
        assert_eq!(slice.get(0), Some(&false));
        assert_eq!(slice.get(7), Some(&true));
        assert_eq!(slice.get(9), Some(&false));
        assert_eq!(slice.get(17), Some(&true));
        let s = slice.iter().fold(String::with_capacity(24), |mut acc, b| {
            acc += if *b { "1" } else { "0" };
            acc
        });
        assert_eq!(&s, "000011110000000001000000");
    }

    #[test]
    fn test_der_bistringobject_asref() {
        fn assert_equal<T: AsRef<[u8]>>(s: T, b: &[u8]) {
            assert_eq!(s.as_ref(), b);
        }
        let b: &[u8] = &[0x0f, 0x00, 0x40];
        let obj = BitStringObject { data: b };
        assert_equal(obj, b);
    }

    #[cfg(feature = "bigint")]
    #[test]
    fn test_der_to_bigint() {
        let obj = BerObject::from_obj(BerObjectContent::Integer(b"\x01\x00\x01"));
        let expected = ::num_bigint::BigInt::from(0x10001);

        assert_eq!(obj.as_bigint(), Some(expected));
    }

    #[cfg(feature = "bigint")]
    #[test]
    fn test_der_to_biguint() {
        let obj = BerObject::from_obj(BerObjectContent::Integer(b"\x01\x00\x01"));
        let expected = ::num_bigint::BigUint::from(0x10001 as u32);

        assert_eq!(obj.as_biguint(), Some(expected));
    }
}
