use crate::ber::*;
use crate::error::*;
use crate::oid::*;
use nom::bytes::streaming::take;
use nom::combinator::{complete, map, verify};
use nom::multi::{many0, many_till};
use nom::number::streaming::be_u8;
use nom::{Err, Needed, Offset};
use rusticata_macros::{combinator::parse_hex_to_u64, custom_check};
use std::borrow::Cow;
use std::convert::{Into, TryFrom};

/// Default maximum recursion limit
pub const MAX_RECURSION: usize = 50;

/// Default maximum object size (2^32)
pub const MAX_OBJECT_SIZE: usize = 4_294_967_295;

/// Skip object content, and return true if object was End-Of-Content
pub(crate) fn ber_skip_object_content<'a>(
    i: &'a [u8],
    hdr: &BerObjectHeader,
    max_depth: usize,
) -> BerResult<'a, bool> {
    if max_depth == 0 {
        return Err(Err::Error(BerError::BerMaxDepth));
    }
    match hdr.len {
        BerSize::Definite(l) => {
            if l == 0 && hdr.tag == BerTag::EndOfContent {
                return Ok((i, true));
            }
            let (i, _) = take(l)(i)?;
            Ok((i, false))
        }
        BerSize::Indefinite => {
            // read objects until EndOfContent (00 00)
            // this is recursive
            let mut i = i;
            loop {
                let (i2, header2) = ber_read_element_header(i)?;
                let (i3, eoc) = ber_skip_object_content(i2, &header2, max_depth - 1)?;
                if eoc {
                    // return false, since top object was not EndOfContent
                    return Ok((i3, false));
                }
                i = i3;
            }
        }
    }
}

/// Read object raw content (bytes)
pub(crate) fn ber_get_object_content<'a>(
    i: &'a [u8],
    hdr: &BerObjectHeader,
    max_depth: usize,
) -> BerResult<'a, &'a [u8]> {
    let start_i = i;
    let (i, _) = ber_skip_object_content(i, hdr, max_depth)?;
    let len = start_i.offset(i);
    let (content, i) = start_i.split_at(len);
    // if len is indefinite, there are 2 extra bytes for EOC
    if hdr.len == BerSize::Indefinite {
        let len = content.len();
        assert!(len >= 2);
        Ok((i, &content[..len - 2]))
    } else {
        Ok((i, content))
    }
}

/// Try to parse input bytes as u64
#[inline]
pub(crate) fn bytes_to_u64(s: &[u8]) -> Result<u64, BerError> {
    let mut u: u64 = 0;
    for &c in s {
        if u & 0xff00_0000_0000_0000 != 0 {
            return Err(BerError::IntegerTooLarge);
        }
        u <<= 8;
        u |= u64::from(c);
    }
    Ok(u)
}

/// Try to parse an input bit string as u64.
///
/// Note: this is for the primitive BER/DER encoding only, the
/// constructed BER encoding for BIT STRING does not seem to be
/// supported at all by the library currently.
#[inline]
pub(crate) fn bitstring_to_u64(
    padding_bits: usize,
    data: &BitStringObject,
) -> Result<u64, BerError> {
    let raw_bytes = data.data;
    let bit_size = (raw_bytes.len() * 8)
        .checked_sub(padding_bits)
        .ok_or(BerError::InvalidLength)?;
    if bit_size > 64 {
        return Err(BerError::IntegerTooLarge);
    }
    let padding_bits = padding_bits % 8;
    let num_bytes = if bit_size % 8 > 0 {
        (bit_size / 8) + 1
    } else {
        bit_size / 8
    };
    let mut resulting_integer: u64 = 0;
    for &c in &raw_bytes[..num_bytes] {
        resulting_integer <<= 8;
        resulting_integer |= c as u64;
    }
    Ok(resulting_integer >> padding_bits)
}

pub(crate) fn parse_identifier(i: &[u8]) -> BerResult<(u8, u8, u32, &[u8])> {
    if i.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let a = i[0] >> 6;
        let b = if i[0] & 0b0010_0000 != 0 { 1 } else { 0 };
        let mut c = u32::from(i[0] & 0b0001_1111);

        let mut tag_byte_count = 1;

        if c == 0x1f {
            c = 0;
            loop {
                // Make sure we don't read past the end of our data.
                custom_check!(i, tag_byte_count >= i.len(), BerError::InvalidTag)?;

                // With tag defined as u32 the most we can fit in is four tag bytes.
                // (X.690 doesn't actually specify maximum tag width.)
                custom_check!(i, tag_byte_count > 5, BerError::InvalidTag)?;

                c = (c << 7) | (u32::from(i[tag_byte_count]) & 0x7f);
                let done = i[tag_byte_count] & 0x80 == 0;
                tag_byte_count += 1;
                if done {
                    break;
                }
            }
        }

        let (raw_tag, rem) = i.split_at(tag_byte_count);

        Ok((rem, (a, b, c, raw_tag)))
    }
}

/// Return the MSB and the rest of the first byte, or an error
pub(crate) fn parse_ber_length_byte(i: &[u8]) -> BerResult<(u8, u8)> {
    if i.is_empty() {
        Err(Err::Incomplete(Needed::new(1)))
    } else {
        let a = i[0] >> 7;
        let b = i[0] & 0b0111_1111;
        Ok((&i[1..], (a, b)))
    }
}

/// Read an object header
///
/// ### Example
///
/// ```
/// # use der_parser::ber::{ber_read_element_header, BerClass, BerSize, BerTag};
/// #
/// let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (i, hdr) = ber_read_element_header(bytes).expect("could not read header");
///
/// assert_eq!(hdr.class, BerClass::Universal);
/// assert_eq!(hdr.tag, BerTag::Integer);
/// assert_eq!(hdr.len, BerSize::Definite(3));
/// ```
pub fn ber_read_element_header(i: &[u8]) -> BerResult<BerObjectHeader> {
    let (i1, el) = parse_identifier(i)?;
    let class = match BerClass::try_from(el.0) {
        Ok(c) => c,
        Err(_) => unreachable!(), // Cannot fail, we have read exactly 2 bits
    };
    let (i2, len) = parse_ber_length_byte(i1)?;
    let (i3, len) = match (len.0, len.1) {
        (0, l1) => {
            // Short form: MSB is 0, the rest encodes the length (which can be 0) (8.1.3.4)
            (i2, BerSize::Definite(usize::from(l1)))
        }
        (_, 0) => {
            // Indefinite form: MSB is 1, the rest is 0 (8.1.3.6)
            // If encoding is primitive, definite form shall be used (8.1.3.2)
            if el.1 == 0 {
                return Err(Err::Error(BerError::ConstructExpected));
            }
            (i2, BerSize::Indefinite)
        }
        (_, l1) => {
            // if len is 0xff -> error (8.1.3.5)
            if l1 == 0b0111_1111 {
                return Err(::nom::Err::Error(BerError::InvalidTag));
            }
            let (i3, llen) = take(l1)(i2)?;
            match bytes_to_u64(llen) {
                Ok(l) => {
                    let l =
                        usize::try_from(l).or(Err(::nom::Err::Error(BerError::InvalidLength)))?;
                    (i3, BerSize::Definite(l))
                }
                Err(_) => {
                    return Err(::nom::Err::Error(BerError::InvalidTag));
                }
            }
        }
    };
    let hdr = BerObjectHeader::new(class, el.1, BerTag(el.2), len).with_raw_tag(Some(el.3));
    Ok((i3, hdr))
}

#[allow(clippy::unnecessary_wraps)]
#[inline]
fn ber_read_content_eoc(i: &[u8]) -> BerResult<BerObjectContent> {
    Ok((i, BerObjectContent::EndOfContent))
}

#[inline]
fn ber_read_content_bool(i: &[u8]) -> BerResult<BerObjectContent> {
    match be_u8(i) {
        Ok((rem, 0)) => Ok((rem, BerObjectContent::Boolean(false))),
        Ok((rem, _)) => Ok((rem, BerObjectContent::Boolean(true))),
        Err(e) => Err(e),
    }
}

#[inline]
fn ber_read_content_integer(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::Integer)(i)
}

#[inline]
fn ber_read_content_bitstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    custom_check!(i, len == 0, BerError::InvalidLength)?;

    let (i, ignored_bits) = be_u8(i)?;
    let (i, data) = take(len - 1)(i)?;
    Ok((
        i,
        BerObjectContent::BitString(ignored_bits, BitStringObject { data }),
    ))
}

#[inline]
fn ber_read_content_octetstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::OctetString)(i)
}

#[allow(clippy::unnecessary_wraps)]
#[inline]
fn ber_read_content_null(i: &[u8]) -> BerResult<BerObjectContent> {
    Ok((i, BerObjectContent::Null))
}

fn ber_read_content_oid(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    custom_check!(i, len == 0, BerError::InvalidLength)?;

    let (i1, oid) = verify(take(len), |os: &[u8]| os.last().unwrap() >> 7 == 0u8)(i)?;

    let obj = BerObjectContent::OID(Oid::new(Cow::Borrowed(oid)));
    Ok((i1, obj))
}

#[inline]
fn ber_read_content_enum(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    let (rem, num) = parse_hex_to_u64(i, len).map_err(|_| BerError::BerValueError)?;
    Ok((rem, BerObjectContent::Enum(num)))
}

fn ber_read_content_utf8string(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    let (i, bytes) = take(len)(i)?;
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::UTF8String(s))?;
    Ok((i, s))
}

fn ber_read_content_relativeoid(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    custom_check!(i, len == 0, BerError::InvalidLength)?;

    let (i1, oid) = verify(take(len), |os: &[u8]| os.last().unwrap() >> 7 == 0u8)(i)?;

    let obj = BerObjectContent::RelativeOID(Oid::new_relative(Cow::Borrowed(oid)));
    Ok((i1, obj))
}

fn ber_read_content_sequence(
    i: &[u8],
    len: BerSize,
    max_depth: usize,
) -> BerResult<BerObjectContent> {
    custom_check!(i, max_depth == 0, BerError::BerMaxDepth)?;
    match len {
        BerSize::Definite(len) => {
            let (i, data) = take(len)(i)?;
            let (_, l) = many0(complete(r_parse_ber(max_depth - 1)))(data)?;
            // trailing bytes are ignored
            Ok((i, BerObjectContent::Sequence(l)))
        }
        BerSize::Indefinite => {
            // indefinite form
            // read until end-of-content
            let (rem, (l, _)) = many_till(r_parse_ber(max_depth - 1), parse_ber_endofcontent)(i)?;
            Ok((rem, BerObjectContent::Sequence(l)))
        }
    }
}

fn ber_read_content_set(i: &[u8], len: BerSize, max_depth: usize) -> BerResult<BerObjectContent> {
    custom_check!(i, max_depth == 0, BerError::BerMaxDepth)?;
    match len {
        BerSize::Definite(len) => {
            let (i, data) = take(len)(i)?;
            let (_, l) = many0(complete(r_parse_ber(max_depth - 1)))(data)?;
            // trailing bytes are ignored
            Ok((i, BerObjectContent::Set(l)))
        }
        BerSize::Indefinite => {
            // indefinite form
            // read until end-of-content
            let (rem, (l, _)) = many_till(r_parse_ber(max_depth - 1), parse_ber_endofcontent)(i)?;
            Ok((rem, BerObjectContent::Set(l)))
        }
    }
}

fn ber_read_content_numericstring<'a>(i: &'a [u8], len: usize) -> BerResult<BerObjectContent<'a>> {
    // Argument must be a reference, because of the .iter().all(F) call below
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn is_numeric(b: &u8) -> bool {
        matches!(*b, b'0'..=b'9' | b' ')
    }
    let (i, bytes) = take(len)(i)?;
    if !bytes.iter().all(is_numeric) {
        return Err(Err::Error(BerError::StringInvalidCharset));
    }
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::NumericString(s))?;
    Ok((i, s))
}

fn ber_read_content_visiblestring<'a>(i: &'a [u8], len: usize) -> BerResult<BerObjectContent<'a>> {
    // Argument must be a reference, because of the .iter().all(F) call below
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn is_visible(b: &u8) -> bool {
        0x20 <= *b && *b <= 0x7f
    }
    let (i, bytes) = take(len)(i)?;
    if !bytes.iter().all(is_visible) {
        return Err(Err::Error(BerError::StringInvalidCharset));
    }
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::VisibleString(s))?;
    Ok((i, s))
}

fn ber_read_content_printablestring<'a>(
    i: &'a [u8],
    len: usize,
) -> BerResult<BerObjectContent<'a>> {
    // Argument must be a reference, because of the .iter().all(F) call below
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn is_printable(b: &u8) -> bool {
        matches!(*b,
            b'a'..=b'z'
            | b'A'..=b'Z'
            | b'0'..=b'9'
            | b' '
            | b'\''
            | b'('
            | b')'
            | b'+'
            | b','
            | b'-'
            | b'.'
            | b'/'
            | b':'
            | b'='
            | b'?')
    }
    let (i, bytes) = take(len)(i)?;
    if !bytes.iter().all(is_printable) {
        return Err(Err::Error(BerError::StringInvalidCharset));
    }
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::PrintableString(s))?;
    Ok((i, s))
}

#[inline]
fn ber_read_content_t61string(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::T61String)(i)
}

#[inline]
fn ber_read_content_videotexstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::VideotexString)(i)
}

fn ber_read_content_ia5string<'a>(i: &'a [u8], len: usize) -> BerResult<BerObjectContent<'a>> {
    let (i, bytes) = take(len)(i)?;
    if !bytes.iter().all(u8::is_ascii) {
        return Err(Err::Error(BerError::StringInvalidCharset));
    }
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::IA5String(s))?;
    Ok((i, s))
}

fn ber_read_content_utctime<'a>(i: &'a [u8], len: usize) -> BerResult<BerObjectContent<'a>> {
    // Argument must be a reference, because of the .iter().all(F) call below
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn is_visible(b: &u8) -> bool {
        0x20 <= *b && *b <= 0x7f
    }
    let (i, bytes) = take(len)(i)?;
    if !bytes.iter().all(is_visible) {
        return Err(Err::Error(BerError::StringInvalidCharset));
    }
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::UTCTime(s))?;
    Ok((i, s))
}

fn ber_read_content_generalizedtime<'a>(
    i: &'a [u8],
    len: usize,
) -> BerResult<BerObjectContent<'a>> {
    // Argument must be a reference, because of the .iter().all(F) call below
    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn is_visible(b: &u8) -> bool {
        0x20 <= *b && *b <= 0x7f
    }
    let (i, bytes) = take(len)(i)?;
    if !bytes.iter().all(is_visible) {
        return Err(Err::Error(BerError::StringInvalidCharset));
    }
    let s = std::str::from_utf8(bytes)
        .map_err(|_| Err::Error(BerError::StringInvalidCharset))
        .map(|s| BerObjectContent::GeneralizedTime(s))?;
    Ok((i, s))
}

#[inline]
fn ber_read_content_objectdescriptor(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::ObjectDescriptor)(i)
}

#[inline]
fn ber_read_content_graphicstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::GraphicString)(i)
}

#[inline]
fn ber_read_content_generalstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::GeneralString)(i)
}

#[inline]
fn ber_read_content_bmpstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::BmpString)(i)
}

#[inline]
fn ber_read_content_universalstring(i: &[u8], len: usize) -> BerResult<BerObjectContent> {
    map(take(len), BerObjectContent::UniversalString)(i)
}

/// Parse the next bytes as the *content* of a BER object.
///
/// Content type is *not* checked to match tag, caller is responsible of providing the correct tag
///
/// This function is mostly used when parsing implicit tagged objects, when reading primitive
/// types.
///
/// `max_depth` is the maximum allowed recursion for objects.
///
/// ### Example
///
/// ```
/// # use der_parser::ber::{ber_read_element_content_as, ber_read_element_header, BerTag};
/// #
/// # let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (i, hdr) = ber_read_element_header(bytes).expect("could not read header");
/// let (_, content) = ber_read_element_content_as(
///     i, hdr.tag, hdr.len, hdr.is_constructed(), 5
/// ).expect("parsing failed");
/// #
/// # assert_eq!(hdr.tag, BerTag::Integer);
/// # assert_eq!(content.as_u32(), Ok(0x10001));
/// ```
pub fn ber_read_element_content_as(
    i: &[u8],
    tag: BerTag,
    len: BerSize,
    constructed: bool,
    max_depth: usize,
) -> BerResult<BerObjectContent> {
    if let BerSize::Definite(l) = len {
        custom_check!(i, l > MAX_OBJECT_SIZE, BerError::InvalidLength)?;
        if i.len() < l {
            return Err(Err::Incomplete(Needed::new(l)));
        }
    }
    match tag {
        // 0x00 end-of-content
        BerTag::EndOfContent => {
            custom_check!(i, len != BerSize::Definite(0), BerError::InvalidLength)?;
            ber_read_content_eoc(i)
        }
        // 0x01 bool
        BerTag::Boolean => {
            let len = len.primitive()?;
            custom_check!(i, len != 1, BerError::InvalidLength)?;
            ber_read_content_bool(i)
        }
        // 0x02
        BerTag::Integer => {
            custom_check!(i, constructed, BerError::ConstructUnexpected)?;
            let len = len.primitive()?;
            ber_read_content_integer(i, len)
        }
        // 0x03: bitstring
        BerTag::BitString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.6.3)
            let len = len.primitive()?;
            ber_read_content_bitstring(i, len)
        }
        // 0x04: octetstring
        BerTag::OctetString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.7.1)
            let len = len.primitive()?;
            ber_read_content_octetstring(i, len)
        }
        // 0x05: null
        BerTag::Null => {
            custom_check!(i, constructed, BerError::ConstructUnexpected)?;
            let len = len.primitive()?;
            custom_check!(i, len != 0, BerError::InvalidLength)?;
            ber_read_content_null(i)
        }
        // 0x06: object identifier
        BerTag::Oid => {
            custom_check!(i, constructed, BerError::ConstructUnexpected)?; // forbidden in 8.19.1
            let len = len.primitive()?;
            ber_read_content_oid(i, len)
        }
        // 0x07: object descriptor - Alias for GraphicString with a different
        // implicit tag, see below
        BerTag::ObjDescriptor => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_objectdescriptor(i, len)
        }
        // 0x0a: enumerated
        BerTag::Enumerated => {
            custom_check!(i, constructed, BerError::ConstructUnexpected)?; // forbidden in 8.4
            let len = len.primitive()?;
            ber_read_content_enum(i, len)
        }
        // 0x0c: UTF8String - Unicode encoded with the UTF-8 charset (ISO/IEC
        // 10646-1, Annex D)
        BerTag::Utf8String => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_utf8string(i, len)
        }
        // 0x0d: relative object identified
        BerTag::RelativeOid => {
            custom_check!(i, constructed, BerError::ConstructUnexpected)?;
            let len = len.primitive()?;
            ber_read_content_relativeoid(i, len)
        }
        // 0x10: sequence
        BerTag::Sequence => {
            custom_check!(i, !constructed, BerError::ConstructExpected)?;
            ber_read_content_sequence(i, len, max_depth)
        }
        // 0x11: set
        BerTag::Set => {
            custom_check!(i, !constructed, BerError::ConstructExpected)?;
            ber_read_content_set(i, len, max_depth)
        }
        // 0x12: numericstring - ASCII string with digits an spaces only
        BerTag::NumericString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_numericstring(i, len)
        }
        // 0x13: printablestring - ASCII string with certain printable
        // characters only (specified in Table 10 of X.680)
        BerTag::PrintableString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_printablestring(i, len)
        }
        // 0x14: t61string - ISO 2022 string with a Teletex (T.61) charset,
        // ASCII is possible but only when explicit escaped, as by default
        // the G0 character range (0x20-0x7f) will match the graphic character
        // set. https://en.wikipedia.org/wiki/ITU_T.61
        BerTag::T61String => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_t61string(i, len)
        }
        // 0x15: videotexstring - ISO 2022 string with a Videotex (T.100/T.101)
        // charset, excluding ASCII. https://en.wikipedia.org/wiki/Videotex_character_set
        BerTag::VideotexString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_videotexstring(i, len)
        }
        // 0x16: ia5string - ASCII string
        BerTag::Ia5String => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_ia5string(i, len)
        }
        // 0x17: utctime - Alias for a VisibleString with a different implicit
        // tag, see below
        BerTag::UtcTime => {
            let len = len.primitive()?;
            ber_read_content_utctime(i, len)
        }
        // 0x18: generalizedtime - Alias for a VisibleString with a different
        // implicit tag, see below
        BerTag::GeneralizedTime => {
            let len = len.primitive()?;
            ber_read_content_generalizedtime(i, len)
        }
        // 0x19: graphicstring - Generic ISO 2022 container with explicit
        // escape sequences, without control characters
        BerTag::GraphicString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_graphicstring(i, len)
        }
        // 0x1a: visiblestring - ASCII string with no control characters except
        // SPACE
        BerTag::VisibleString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_visiblestring(i, len)
        }
        // 0x1b: generalstring - Generic ISO 2022 container with explicit
        // escape sequences
        BerTag::GeneralString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_generalstring(i, len)
        }
        // 0x1e: bmpstring - Unicode encoded with the UCS-2 big-endian charset
        // (ISO/IEC 10646-1, section 13.1), restricted to the BMP (Basic
        // Multilingual Plane) except certain control cahracters
        BerTag::BmpString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_bmpstring(i, len)
        }
        // 0x1c: universalstring - Unicode encoded with the UCS-4 big-endian
        // charset (ISO/IEC 10646-1, section 13.2)
        BerTag::UniversalString => {
            custom_check!(i, constructed, BerError::Unsupported)?; // XXX valid in BER (8.21)
            let len = len.primitive()?;
            ber_read_content_universalstring(i, len)
        }
        // all unknown values
        _ => Err(Err::Error(BerError::UnknownTag)),
    }
}

/// Parse the next bytes as the content of a BER object (combinator, header reference)
///
/// Content type is *not* checked to match tag, caller is responsible of providing the correct tag
///
/// Caller is also responsible to check if parsing function consumed the expected number of
/// bytes (`header.len`).
///
/// The arguments of the parse function are: `(input, ber_object_header, max_recursion)`.
///
/// This function differs from [`parse_ber_content2`](fn.parse_ber_content2.html) because it passes
/// the BER object header by reference (required for ex. by `parse_ber_implicit`).
///
/// Example: manually parsing header and content
///
/// ```
/// # use der_parser::ber::*;
/// #
/// # let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (i, header) = ber_read_element_header(bytes).expect("parsing failed");
/// let (rem, content) = parse_ber_content(header.tag)(i, &header, MAX_RECURSION)
///     .expect("parsing failed");
/// #
/// # assert_eq!(header.tag, BerTag::Integer);
/// ```
pub fn parse_ber_content<'a>(
    tag: BerTag,
) -> impl Fn(&'a [u8], &'_ BerObjectHeader, usize) -> BerResult<'a, BerObjectContent<'a>> {
    move |i: &[u8], hdr: &BerObjectHeader, max_recursion: usize| {
        ber_read_element_content_as(i, tag, hdr.len, hdr.is_constructed(), max_recursion)
    }
}

/// Parse the next bytes as the content of a BER object (combinator, owned header)
///
/// Content type is *not* checked to match tag, caller is responsible of providing the correct tag
///
/// Caller is also responsible to check if parsing function consumed the expected number of
/// bytes (`header.len`).
///
/// The arguments of the parse function are: `(input, ber_object_header, max_recursion)`.
///
/// This function differs from [`parse_ber_content`](fn.parse_ber_content.html) because it passes
/// an owned BER object header (required for ex. by `parse_ber_tagged_implicit_g`).
///
/// Example: manually parsing header and content
///
/// ```
/// # use der_parser::ber::*;
/// #
/// # let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (i, header) = ber_read_element_header(bytes).expect("parsing failed");
/// let (rem, content) = parse_ber_content(header.tag)(i, &header, MAX_RECURSION)
///     .expect("parsing failed");
/// #
/// # assert_eq!(header.tag, BerTag::Integer);
/// ```
pub fn parse_ber_content2<'a>(
    tag: BerTag,
) -> impl Fn(&'a [u8], BerObjectHeader<'a>, usize) -> BerResult<'a, BerObjectContent<'a>> {
    move |i: &[u8], hdr: BerObjectHeader, max_recursion: usize| {
        ber_read_element_content_as(i, tag, hdr.len, hdr.is_constructed(), max_recursion)
    }
}

/// Parse a BER object, expecting a value with specified tag
///
/// The object is parsed recursively, with a maximum depth of `MAX_RECURSION`.
///
/// ### Example
///
/// ```
/// use der_parser::ber::BerTag;
/// use der_parser::ber::parse_ber_with_tag;
///
/// let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (_, obj) = parse_ber_with_tag(bytes, BerTag::Integer).expect("parsing failed");
///
/// assert_eq!(obj.header.tag, BerTag::Integer);
/// ```
pub fn parse_ber_with_tag<Tag: Into<BerTag>>(i: &[u8], tag: Tag) -> BerResult {
    let tag = tag.into();
    let (i, hdr) = ber_read_element_header(i)?;
    if hdr.tag != tag {
        return Err(nom::Err::Error(BerError::InvalidTag));
    }
    let (i, content) =
        ber_read_element_content_as(i, hdr.tag, hdr.len, hdr.is_constructed(), MAX_RECURSION)?;
    Ok((i, BerObject::from_header_and_content(hdr, content)))
}

/// Read end of content marker
#[inline]
pub fn parse_ber_endofcontent(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::EndOfContent)
}

/// Read a boolean value
///
/// The encoding of a boolean value shall be primitive. The contents octets shall consist of a
/// single octet.
///
/// If the boolean value is FALSE, the octet shall be zero.
/// If the boolean value is TRUE, the octet shall be one byte, and have all bits set to one (0xff).
#[inline]
pub fn parse_ber_bool(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Boolean)
}

/// Read an integer value
///
/// The encoding of a boolean value shall be primitive. The contents octets shall consist of one or
/// more octets.
///
/// To access the content, use the [`as_u64`](struct.BerObject.html#method.as_u64),
/// [`as_u32`](struct.BerObject.html#method.as_u32),
/// [`as_biguint`](struct.BerObject.html#method.as_biguint) or
/// [`as_bigint`](struct.BerObject.html#method.as_bigint) methods.
/// Remember that a BER integer has unlimited size, so these methods return `Result` or `Option`
/// objects.
///
/// # Examples
///
/// ```rust
/// # extern crate nom;
/// # use der_parser::ber::parse_ber_integer;
/// # use der_parser::ber::{BerObject,BerObjectContent};
/// let empty = &b""[..];
/// let bytes = [0x02, 0x03, 0x01, 0x00, 0x01];
/// let expected  = BerObject::from_obj(BerObjectContent::Integer(b"\x01\x00\x01"));
/// assert_eq!(
///     parse_ber_integer(&bytes),
///     Ok((empty, expected))
/// );
/// ```
#[inline]
pub fn parse_ber_integer(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Integer)
}

/// Read an bitstring value
#[inline]
pub fn parse_ber_bitstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::BitString)
}

/// Read an octetstring value
#[inline]
pub fn parse_ber_octetstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::OctetString)
}

/// Read a null value
#[inline]
pub fn parse_ber_null(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Null)
}

/// Read an object identifier value
#[inline]
pub fn parse_ber_oid(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Oid)
}

/// Read an enumerated value
#[inline]
pub fn parse_ber_enum(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Enumerated)
}

/// Read a UTF-8 string value. The encoding is checked.
#[inline]
pub fn parse_ber_utf8string(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Utf8String)
}

/// Read a relative object identifier value
#[inline]
pub fn parse_ber_relative_oid(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::RelativeOid)
}

/// Parse a sequence of BER elements
///
/// Read a sequence of BER objects, without any constraint on the types.
/// Sequence is parsed recursively, so if structured elements are found, they are parsed using the
/// same function.
///
/// To read a specific sequence of objects (giving the expected types), use the
/// [`parse_ber_sequence_defined`](macro.parse_ber_sequence_defined.html) macro.
#[inline]
pub fn parse_ber_sequence(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Sequence)
}

/// Parse a set of BER elements
///
/// Read a set of BER objects, without any constraint on the types.
/// Set is parsed recursively, so if structured elements are found, they are parsed using the
/// same function.
///
/// To read a specific set of objects (giving the expected types), use the
/// [`parse_ber_set_defined`](macro.parse_ber_set_defined.html) macro.
#[inline]
pub fn parse_ber_set(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Set)
}

/// Read a numeric string value. The content is verified to
/// contain only digits and spaces.
#[inline]
pub fn parse_ber_numericstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::NumericString)
}

/// Read a visible string value. The content is verified to
/// contain only the allowed characters.
#[inline]
pub fn parse_ber_visiblestring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::VisibleString)
}

/// Read a printable string value. The content is verified to
/// contain only the allowed characters.
#[inline]
pub fn parse_ber_printablestring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::PrintableString)
}

/// Read a T61 string value
#[inline]
pub fn parse_ber_t61string(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::T61String)
}

/// Read a Videotex string value
#[inline]
pub fn parse_ber_videotexstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::VideotexString)
}

/// Read an IA5 string value. The content is verified to be ASCII.
#[inline]
pub fn parse_ber_ia5string(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::Ia5String)
}

/// Read an UTC time value
#[inline]
pub fn parse_ber_utctime(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::UtcTime)
}

/// Read a Generalized time value
#[inline]
pub fn parse_ber_generalizedtime(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::GeneralizedTime)
}

/// Read an ObjectDescriptor value
#[inline]
pub fn parse_ber_objectdescriptor(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::ObjDescriptor)
}

/// Read a GraphicString value
#[inline]
pub fn parse_ber_graphicstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::GraphicString)
}

/// Read a GeneralString value
#[inline]
pub fn parse_ber_generalstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::GeneralString)
}

/// Read a BmpString value
#[inline]
pub fn parse_ber_bmpstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::BmpString)
}

/// Read a UniversalString value
#[inline]
pub fn parse_ber_universalstring(i: &[u8]) -> BerResult {
    parse_ber_with_tag(i, BerTag::UniversalString)
}

/// Parse an optional tagged object, applying function to get content
///
/// This function returns a `BerObject`, trying to read content as generic BER objects.
/// If parsing failed, return an optional object containing `None`.
///
/// To support other return or error types, use
/// [parse_ber_tagged_explicit_g](fn.parse_ber_tagged_explicit_g.html)
///
/// This function will never fail: if parsing content failed, the BER value `Optional(None)` is
/// returned.
pub fn parse_ber_explicit_optional<F>(i: &[u8], tag: BerTag, f: F) -> BerResult
where
    F: Fn(&[u8]) -> BerResult,
{
    parse_ber_optional(parse_ber_tagged_explicit_g(tag, |content, hdr| {
        let (rem, obj) = f(content)?;
        let content = BerObjectContent::Tagged(hdr.class, hdr.tag, Box::new(obj));
        let tagged = BerObject::from_header_and_content(hdr, content);
        Ok((rem, tagged))
    }))(i)
}

/// Parse an optional tagged object, applying function to get content
///
/// This function is deprecated, use
/// [parse_ber_explicit_optional](fn.parse_ber_explicit_optional.html) instead.
#[deprecated(
    since = "5.0.0",
    note = "Please use `parse_ber_explicit_optional` instead"
)]
#[inline]
pub fn parse_ber_explicit<F>(i: &[u8], tag: BerTag, f: F) -> BerResult
where
    F: Fn(&[u8]) -> BerResult,
{
    parse_ber_explicit_optional(i, tag, f)
}

/// Parse an implicit tagged object, applying function to read content
///
/// Note: unlike explicit tagged functions, the callback must be a *content* parsing function,
/// often based on the [`parse_ber_content`](fn.parse_ber_content.html) combinator.
///
/// The built object will use the original header (and tag), so the content may not match the tag
/// value.
///
/// For a combinator version, see [parse_ber_tagged_implicit](fn.parse_ber_tagged_implicit.html).
///
/// For a generic version (different output and error types), see
/// [parse_ber_tagged_implicit_g](fn.parse_ber_tagged_implicit_g.html).
///
/// # Examples
///
/// The following parses `[3] IMPLICIT INTEGER` into a `BerObject`:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// #
/// fn parse_int_implicit(i:&[u8]) -> BerResult<BerObject> {
///     parse_ber_implicit(
///         i,
///         3,
///         parse_ber_content(BerTag::Integer),
///     )
/// }
///
/// # let bytes = &[0x83, 0x03, 0x01, 0x00, 0x01];
/// let res = parse_int_implicit(bytes);
/// # match res {
/// #     Ok((rem, content)) => {
/// #         assert!(rem.is_empty());
/// #         assert_eq!(content.as_u32(), Ok(0x10001));
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
#[inline]
pub fn parse_ber_implicit<'a, Tag, F>(i: &'a [u8], tag: Tag, f: F) -> BerResult<'a>
where
    F: Fn(&'a [u8], &'_ BerObjectHeader, usize) -> BerResult<'a, BerObjectContent<'a>>,
    Tag: Into<BerTag>,
{
    parse_ber_tagged_implicit(tag, f)(i)
}

/// Combinator for building optional BER values
///
/// To read optional BER values, it is to use the nom `opt()` combinator. However, this results in
/// a `Option<BerObject>` and prevents using some functions from this crate (the generic functions
/// can still be used).
///
/// This combinator is used when parsing BER values, while keeping `BerObject` output only.
///
/// This function will never fail: if parsing content failed, the BER value `Optional(None)` is
/// returned.
///
/// ### Example
///
/// ```
/// # use der_parser::ber::*;
/// #
/// let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let mut parser = parse_ber_optional(parse_ber_integer);
/// let (_, obj) = parser(bytes).expect("parsing failed");
///
/// assert_eq!(obj.header.tag, BerTag::Integer);
/// assert!(obj.as_optional().is_ok());
/// ```
pub fn parse_ber_optional<'a, F>(mut f: F) -> impl FnMut(&'a [u8]) -> BerResult<'a>
where
    F: FnMut(&'a [u8]) -> BerResult<'a>,
{
    move |i: &[u8]| {
        let res = f(i);
        match res {
            Ok((rem, inner)) => {
                let opt = BerObject::from_header_and_content(
                    inner.header.clone(),
                    BerObjectContent::Optional(Some(Box::new(inner))),
                );
                Ok((rem, opt))
            }
            Err(_) => Ok((i, BerObject::from_obj(BerObjectContent::Optional(None)))),
        }
    }
}

/// Parse BER object and try to decode it as a 32-bits unsigned integer
///
/// Return `IntegerTooLarge` if object is an integer, but can not be represented in the target
/// integer type.
#[inline]
pub fn parse_ber_u32(i: &[u8]) -> BerResult<u32> {
    parse_ber_container(|content, hdr| {
        if hdr.tag != BerTag::Integer {
            return Err(Err::Error(BerError::InvalidTag));
        }
        let l = bytes_to_u64(content)?;
        if l > 0xffff_ffff {
            Err(Err::Error(BerError::IntegerTooLarge))
        } else {
            Ok((&b""[..], l as u32))
        }
    })(i)
}

/// Parse BER object and try to decode it as a 64-bits unsigned integer
///
/// Return `IntegerTooLarge` if object is an integer, but can not be represented in the target
/// integer type.
#[inline]
pub fn parse_ber_u64(i: &[u8]) -> BerResult<u64> {
    parse_ber_container(|content, hdr| {
        if hdr.tag != BerTag::Integer {
            return Err(Err::Error(BerError::InvalidTag));
        }
        let l = bytes_to_u64(content)?;
        Ok((&b""[..], l))
    })(i)
}

/// Parse BER object and get content as slice
#[inline]
pub fn parse_ber_slice<Tag: Into<BerTag>>(i: &[u8], tag: Tag) -> BerResult<&[u8]> {
    let tag = tag.into();
    parse_ber_container(move |content, hdr| {
        if hdr.tag != tag {
            return Err(Err::Error(BerError::InvalidTag));
        }
        Ok((&b""[..], content))
    })(i)
}

/// Helper combinator, to create a parser with a maximum parsing depth
#[inline]
pub(crate) fn r_parse_ber(max_depth: usize) -> impl Fn(&[u8]) -> BerResult {
    move |i: &[u8]| parse_ber_recursive(i, max_depth)
}

/// Parse BER object recursively, specifying the maximum recursion depth
///
/// Return a tuple containing the remaining (unparsed) bytes and the BER Object, or an error.
///
/// ### Example
///
/// ```
/// use der_parser::ber::{parse_ber_recursive, BerTag};
///
/// let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (_, obj) = parse_ber_recursive(bytes, 1).expect("parsing failed");
///
/// assert_eq!(obj.header.tag, BerTag::Integer);
/// ```
pub fn parse_ber_recursive(i: &[u8], max_depth: usize) -> BerResult {
    custom_check!(i, max_depth == 0, BerError::BerMaxDepth)?;
    let (rem, hdr) = ber_read_element_header(i)?;
    if let BerSize::Definite(l) = hdr.len {
        custom_check!(i, l > MAX_OBJECT_SIZE, BerError::InvalidLength)?;
    }
    match hdr.class {
        BerClass::Universal | BerClass::Private => (),
        _ => {
            let (rem, content) = ber_get_object_content(rem, &hdr, max_depth)?;
            let content = BerObjectContent::Unknown(hdr.tag, content);
            let obj = BerObject::from_header_and_content(hdr, content);
            return Ok((rem, obj));
        }
    }
    match ber_read_element_content_as(rem, hdr.tag, hdr.len, hdr.is_constructed(), max_depth) {
        Ok((rem, content)) => Ok((rem, BerObject::from_header_and_content(hdr, content))),
        Err(Err::Error(BerError::UnknownTag)) => {
            let (rem, content) = ber_get_object_content(rem, &hdr, max_depth)?;
            let content = BerObjectContent::Unknown(hdr.tag, content);
            let obj = BerObject::from_header_and_content(hdr, content);
            Ok((rem, obj))
        }
        Err(e) => Err(e),
    }
}

/// Parse BER object recursively
///
/// Return a tuple containing the remaining (unparsed) bytes and the BER Object, or an error.
///
/// *Note*: this is the same as calling `parse_ber_recursive` with `MAX_RECURSION`.
///
/// ### Example
///
/// ```
/// use der_parser::ber::{parse_ber, BerTag};
///
/// let bytes = &[0x02, 0x03, 0x01, 0x00, 0x01];
/// let (_, obj) = parse_ber(bytes).expect("parsing failed");
///
/// assert_eq!(obj.header.tag, BerTag::Integer);
/// ```
#[inline]
pub fn parse_ber(i: &[u8]) -> BerResult {
    parse_ber_recursive(i, MAX_RECURSION)
}

#[test]
fn test_numericstring() {
    assert_eq!(
        ber_read_content_numericstring(b" 0123  4495768 ", 15),
        Ok((
            [].as_ref(),
            BerObjectContent::NumericString(" 0123  4495768 ")
        )),
    );
    assert_eq!(
        ber_read_content_numericstring(b"", 0),
        Ok(([].as_ref(), BerObjectContent::NumericString(""))),
    );
    assert!(ber_read_content_numericstring(b"123a", 4).is_err());
}

#[test]
fn text_visiblestring() {
    assert_eq!(
        ber_read_content_visiblestring(b"AZaz]09 '()+,-./:=?", 19),
        Ok((
            [].as_ref(),
            BerObjectContent::VisibleString("AZaz]09 '()+,-./:=?")
        )),
    );
    assert_eq!(
        ber_read_content_visiblestring(b"", 0),
        Ok(([].as_ref(), BerObjectContent::VisibleString(""))),
    );
    assert!(ber_read_content_visiblestring(b"\n", 1).is_err());
}

#[test]
fn test_printablestring() {
    assert_eq!(
        ber_read_content_printablestring(b"AZaz09 '()+,-./:=?", 18),
        Ok((
            [].as_ref(),
            BerObjectContent::PrintableString("AZaz09 '()+,-./:=?")
        )),
    );
    assert_eq!(
        ber_read_content_printablestring(b"", 0),
        Ok(([].as_ref(), BerObjectContent::PrintableString(""))),
    );
    assert!(ber_read_content_printablestring(b"]\n", 2).is_err());
}

#[test]
fn test_ia5string() {
    assert_eq!(
        ber_read_content_ia5string(b"AZaz\n09 '()+,-./:=?[]{}\0\n", 25),
        Ok((
            [].as_ref(),
            BerObjectContent::IA5String("AZaz\n09 '()+,-./:=?[]{}\0\n")
        )),
    );
    assert_eq!(
        ber_read_content_ia5string(b"", 0),
        Ok(([].as_ref(), BerObjectContent::IA5String(""))),
    );
    assert!(ber_read_content_ia5string(b"\xFF", 1).is_err());
}

#[test]
fn test_utf8string() {
    assert_eq!(
        ber_read_content_utf8string("AZaz09 '()+,-./:=?[]{}\0\nüÜ".as_ref(), 28),
        Ok((
            [].as_ref(),
            BerObjectContent::UTF8String("AZaz09 '()+,-./:=?[]{}\0\nüÜ")
        )),
    );
    assert_eq!(
        ber_read_content_utf8string(b"", 0),
        Ok(([].as_ref(), BerObjectContent::UTF8String(""))),
    );
    assert!(ber_read_content_utf8string(b"\xe2\x28\xa1", 3).is_err());
}

#[test]
fn test_bitstring_to_u64() {
    // ignored bits modulo 8 to 0
    let data = &hex_literal::hex!("0d 71 82");
    let r = bitstring_to_u64(8, &BitStringObject { data });
    assert_eq!(r, Ok(0x0d71));

    // input too large to fit a 64-bits integer
    let data = &hex_literal::hex!("0d 71 82 0e 73 72 76 6e 67 6e 62 6c 6e 2d 65 78 30 31");
    let r = bitstring_to_u64(0, &BitStringObject { data });
    assert!(r.is_err());

    // test large number but with many ignored bits
    let data = &hex_literal::hex!("0d 71 82 0e 73 72 76 6e 67 6e 62 6c 6e 2d 65 78 30 31");
    let r = bitstring_to_u64(130, &BitStringObject { data });
    // 2 = 130 % 8
    assert_eq!(r, Ok(0x0d71 >> 2));
}
