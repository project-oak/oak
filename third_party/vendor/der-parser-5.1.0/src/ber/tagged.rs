use crate::ber::*;
use crate::error::*;
use nom::error::ParseError;
use nom::{Err, IResult};

/// Read a TAGGED EXPLICIT value (combinator)
///
/// The built object will use the outer header (and tag), and contains a `Tagged` object
/// with class, value and content.
///
/// For a generic version (different output and error types), see
/// [parse_ber_tagged_explicit_g](fn.parse_ber_tagged_explicit_g.html).
///
/// The following parses `[2] EXPLICIT INTEGER`:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// use nom::combinator::map_res;
/// #
/// fn parse_int_explicit(i:&[u8]) -> BerResult<u32> {
///    map_res(
///        parse_ber_tagged_explicit(2, parse_ber_integer),
///        |x: BerObject| x.as_tagged()?.2.as_u32()
///    )(i)
/// }
///
/// # let bytes = &[0xa2, 0x05, 0x02, 0x03, 0x01, 0x00, 0x01];
/// let res = parse_int_explicit(bytes);
/// # match res {
/// #     Ok((rem,val)) => {
/// #         assert!(rem.is_empty());
/// #         assert_eq!(val, 0x10001);
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
pub fn parse_ber_tagged_explicit<'a, Tag, F>(tag: Tag, f: F) -> impl FnMut(&'a [u8]) -> BerResult
where
    F: Fn(&'a [u8]) -> BerResult<BerObject>,
    Tag: Into<BerTag>,
{
    let tag = tag.into();
    parse_ber_tagged_explicit_g(tag, move |content, hdr| {
        let (rem, obj) = f(content)?;
        let class = hdr.class;
        let obj2 = BerObject::from_header_and_content(
            hdr,
            BerObjectContent::Tagged(class, tag, Box::new(obj)),
        );
        Ok((rem, obj2))
    })
}

/// Read a TAGGED EXPLICIT value (generic version)
///
/// The following parses `[2] EXPLICIT INTEGER`:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// #
/// fn parse_int_explicit(i:&[u8]) -> BerResult<u32> {
///     parse_ber_tagged_explicit_g(2, move |content, hdr| {
///         let (rem, obj) = parse_ber_integer(content)?;
///         let value = obj.as_u32()?;
///         Ok((rem, value))
///    })(i)
/// }
///
/// # let bytes = &[0xa2, 0x05, 0x02, 0x03, 0x01, 0x00, 0x01];
/// let res = parse_int_explicit(bytes);
/// # match res {
/// #     Ok((rem,val)) => {
/// #         assert!(rem.is_empty());
/// #         assert_eq!(val, 0x10001);
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
pub fn parse_ber_tagged_explicit_g<'a, Tag, Output, F, E>(
    tag: Tag,
    f: F,
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Output, E>
where
    F: Fn(&'a [u8], BerObjectHeader<'a>) -> IResult<&'a [u8], Output, E>,
    E: ParseError<&'a [u8]> + From<BerError>,
    Tag: Into<BerTag>,
{
    let tag = tag.into();
    parse_ber_container(move |i, hdr| {
        if hdr.class == BerClass::Universal {
            return Err(Err::Error(BerError::InvalidClass.into()));
        }
        if hdr.tag != tag {
            return Err(Err::Error(BerError::InvalidTag.into()));
        }
        // X.690 8.14.2: if implicit tagging was not used, the encoding shall be constructed
        if !hdr.is_constructed() {
            return Err(Err::Error(BerError::ConstructExpected.into()));
        }
        f(i, hdr)
        // trailing bytes are ignored
    })
}

/// Read a TAGGED IMPLICIT value (combinator)
///
/// Parse a TAGGED IMPLICIT value, given the expected tag, and the content parsing function.
///
/// The built object will use the original header (and tag), so the content may not match the tag
/// value.
///
/// For a generic version (different output and error types), see
/// [parse_ber_tagged_implicit_g](fn.parse_ber_tagged_implicit_g.html).
///
/// # Examples
///
/// The following parses `[2] IMPLICIT INTEGER` into a `BerObject`:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// #
/// fn parse_int_implicit(i:&[u8]) -> BerResult<BerObject> {
///     parse_ber_tagged_implicit(
///         2,
///         parse_ber_content(BerTag::Integer),
///     )(i)
/// }
///
/// # let bytes = &[0x82, 0x03, 0x01, 0x00, 0x01];
/// let res = parse_int_implicit(bytes);
/// # match res {
/// #     Ok((rem, content)) => {
/// #         assert!(rem.is_empty());
/// #         assert_eq!(content.as_u32(), Ok(0x10001));
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
///
/// The following parses `[2] IMPLICIT INTEGER` into an `u32`, raising an error if the integer is
/// too large:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// use nom::combinator::map_res;
/// #
/// fn parse_int_implicit(i:&[u8]) -> BerResult<u32> {
///     map_res(
///         parse_ber_tagged_implicit(
///             2,
///             parse_ber_content(BerTag::Integer),
///         ),
///         |x: BerObject| x.as_u32()
///     )(i)
/// }
///
/// # let bytes = &[0x82, 0x03, 0x01, 0x00, 0x01];
/// let res = parse_int_implicit(bytes);
/// # match res {
/// #     Ok((rem, val)) => {
/// #         assert!(rem.is_empty());
/// #         assert_eq!(val, 0x10001);
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
pub fn parse_ber_tagged_implicit<'a, Tag, F>(tag: Tag, f: F) -> impl FnMut(&'a [u8]) -> BerResult
where
    F: Fn(&'a [u8], &'_ BerObjectHeader, usize) -> BerResult<'a, BerObjectContent<'a>>,
    Tag: Into<BerTag>,
{
    let tag = tag.into();
    parse_ber_tagged_implicit_g(tag, move |i, hdr, depth| {
        let (rem, content) = f(i, &hdr, depth)?;
        // trailing bytes are ignored
        let obj = BerObject::from_header_and_content(hdr, content);
        Ok((rem, obj))
    })
}

/// Read a TAGGED IMPLICIT value (generic version)
///
/// Parse a TAGGED IMPLICIT value, given the expected tag, and the content parsing function.
///
/// # Examples
///
/// The following parses `[1] IMPLICIT OCTETSTRING`, returning a `BerObject`:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// #
/// fn parse_implicit_0_octetstring(i:&[u8]) -> BerResult<BerObjectContent> {
///     parse_ber_tagged_implicit_g(
///         2,
///         parse_ber_content2(BerTag::OctetString)
///     )(i)
/// }
///
/// # let bytes = &[0x02, 0x05, 0x68, 0x65, 0x6c, 0x6c, 0x6f];
/// let res = parse_implicit_0_octetstring(bytes);
/// # match res {
/// #     Ok((rem, val)) => {
/// #         assert!(rem.is_empty());
/// #         let s = val.as_slice().unwrap();
/// #         assert_eq!(s, b"hello");
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
///
/// The following parses `[2] IMPLICIT INTEGER` into an `u32`, raising an error if the integer is
/// too large:
///
/// ```rust
/// # use der_parser::ber::*;
/// # use der_parser::error::BerResult;
/// #
/// fn parse_int_implicit(i:&[u8]) -> BerResult<u32> {
///     parse_ber_tagged_implicit_g(
///         2,
///         |content, hdr, depth| {
///             let (rem, obj_content) = parse_ber_content(BerTag::Integer)(content, &hdr, depth)?;
///             let value = obj_content.as_u32()?;
///             Ok((rem, value))
///         }
///     )(i)
/// }
///
/// # let bytes = &[0x82, 0x03, 0x01, 0x00, 0x01];
/// let res = parse_int_implicit(bytes);
/// # match res {
/// #     Ok((rem, val)) => {
/// #         assert!(rem.is_empty());
/// #         assert_eq!(val, 0x10001);
/// #     },
/// #     _ => assert!(false)
/// # }
/// ```
pub fn parse_ber_tagged_implicit_g<'a, Tag, Output, F, E>(
    tag: Tag,
    f: F,
) -> impl FnMut(&'a [u8]) -> IResult<&[u8], Output, E>
where
    F: Fn(&'a [u8], BerObjectHeader<'a>, usize) -> IResult<&'a [u8], Output, E>,
    E: ParseError<&'a [u8]> + From<BerError>,
    Tag: Into<BerTag>,
{
    let tag = tag.into();
    parse_ber_container(move |i, hdr| {
        if hdr.tag != tag {
            return Err(Err::Error(BerError::InvalidTag.into()));
        }
        // XXX MAX_RECURSION should not be used, it resets the depth counter
        f(i, hdr, MAX_RECURSION)
        // trailing bytes are ignored
    })
}
