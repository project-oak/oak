use der_parser::ber::*;
use der_parser::error::*;
use der_parser::*;
use hex_literal::hex;
use nom::combinator::map;
use nom::error::ErrorKind;
use nom::sequence::tuple;
use nom::*;
use oid::Oid;
use pretty_assertions::assert_eq;
use test_case::test_case;

#[derive(Debug, PartialEq)]
struct MyStruct<'a> {
    a: BerObject<'a>,
    b: BerObject<'a>,
}

fn parse_struct01(i: &[u8]) -> BerResult<MyStruct> {
    parse_der_struct!(
        i,
        a: parse_ber_integer >> b: parse_ber_integer >> (MyStruct { a, b })
    )
}

fn parse_struct01_complete(i: &[u8]) -> BerResult<MyStruct> {
    parse_der_struct!(
        i,
        a: parse_ber_integer >> b: parse_ber_integer >> eof!() >> (MyStruct { a, b })
    )
}

// calling user function
#[allow(dead_code)]
fn parse_struct02(i: &[u8]) -> BerResult<()> {
    parse_der_struct!(i, _a: parse_ber_integer >> _b: parse_struct01 >> (()))
}

// embedded DER structs
#[allow(dead_code)]
fn parse_struct03(i: &[u8]) -> BerResult<()> {
    parse_der_struct!(
        i,
        _a: parse_ber_integer >> _b: parse_der_struct!(parse_ber_integer >> (())) >> (())
    )
}

// verifying tag
fn parse_struct04(i: &[u8], tag: BerTag) -> BerResult<MyStruct> {
    parse_der_struct!(
        i,
        TAG tag,
        a: parse_ber_integer >>
        b: parse_ber_integer >>
           eof!() >>
        ( MyStruct{ a, b } )
    )
}

#[test_case(&hex!("30 00"), Ok(&[]) ; "empty seq")]
#[test_case(&hex!("30 0a 02 03 01 00 01 02 03 01 00 00"), Ok(&[0x10001, 0x10000]) ; "seq ok")]
#[test_case(&hex!("30 07 02 03 01 00 01 02 03 01"), Err(Err::Error(BerError::NomError(ErrorKind::Eof))) ; "incomplete")]
#[test_case(&hex!("31 0a 02 03 01 00 01 02 03 01 00 00"), Err(Err::Error(BerError::InvalidTag)) ; "invalid tag")]
#[test_case(&hex!("30 80 02 03 01 00 01 00 00"), Ok(&[0x10001]) ; "indefinite seq ok")]
#[test_case(&hex!("30 80"), Err(Err::Incomplete(Needed::new(1))) ; "indefinite incomplete")]
fn tc_ber_seq_of(i: &[u8], out: Result<&[u32], Err<BerError>>) {
    fn parser(i: &[u8]) -> BerResult {
        parse_ber_sequence_of(parse_ber_integer)(i)
    }
    let res = parser(i);
    match out {
        Ok(l) => {
            let (rem, res) = res.expect("could not parse sequence of");
            assert!(rem.is_empty());
            if let BerObjectContent::Sequence(res) = res.content {
                pretty_assertions::assert_eq!(res.len(), l.len());
                for (a, b) in res.iter().zip(l.iter()) {
                    pretty_assertions::assert_eq!(a.as_u32().unwrap(), *b);
                }
            } else {
                panic!("wrong type for parsed object");
            }
        }
        Err(e) => {
            pretty_assertions::assert_eq!(res, Err(e));
        }
    }
}

#[test_case(&hex!("30 0a 02 03 01 00 01 02 03 01 00 00"), Ok(&[0x10001, 0x10000]) ; "seq ok")]
#[test_case(&hex!("30 07 02 03 01 00 01 02 01"), Err(Err::Incomplete(Needed::new(1))) ; "incomplete")]
#[test_case(&hex!("31 0a 02 03 01 00 01 02 03 01 00 00"), Err(Err::Error(BerError::InvalidTag)) ; "invalid tag")]
#[test_case(&hex!("30 80 02 03 01 00 01 02 03 01 00 00 00 00"), Ok(&[0x10001, 0x10000]) ; "indefinite seq")]
fn tc_ber_seq_defined(i: &[u8], out: Result<&[u32], Err<BerError>>) {
    fn parser(i: &[u8]) -> BerResult<BerObject> {
        parse_ber_sequence_defined(map(
            tuple((parse_ber_integer, parse_ber_integer)),
            |(a, b)| vec![a, b],
        ))(i)
    }
    let res = parser(i);
    match out {
        Ok(l) => {
            let (rem, res) = res.expect("could not parse sequence");
            assert!(rem.is_empty());
            if let BerObjectContent::Sequence(res) = res.content {
                pretty_assertions::assert_eq!(res.len(), l.len());
                for (a, b) in res.iter().zip(l.iter()) {
                    pretty_assertions::assert_eq!(a.as_u32().unwrap(), *b);
                }
            } else {
                panic!("wrong type for parsed object");
            }
        }
        Err(e) => {
            pretty_assertions::assert_eq!(res, Err(e));
        }
    }
}

#[test_case(&hex!("31 00"), Ok(&[]) ; "empty set")]
#[test_case(&hex!("31 0a 02 03 01 00 01 02 03 01 00 00"), Ok(&[0x10001, 0x10000]) ; "set ok")]
#[test_case(&hex!("31 07 02 03 01 00 01 02 03 01"), Err(Err::Error(BerError::NomError(ErrorKind::Eof))) ; "incomplete")]
#[test_case(&hex!("30 0a 02 03 01 00 01 02 03 01 00 00"), Err(Err::Error(BerError::InvalidTag)) ; "invalid tag")]
#[test_case(&hex!("31 80 02 03 01 00 01 00 00"), Ok(&[0x10001]) ; "indefinite set ok")]
#[test_case(&hex!("31 80"), Err(Err::Incomplete(Needed::new(1))) ; "indefinite incomplete")]
fn tc_ber_set_of(i: &[u8], out: Result<&[u32], Err<BerError>>) {
    fn parser(i: &[u8]) -> BerResult {
        parse_ber_set_of(parse_ber_integer)(i)
    }
    let res = parser(i);
    match out {
        Ok(l) => {
            let (rem, res) = res.expect("could not parse set of");
            assert!(rem.is_empty());
            if let BerObjectContent::Set(res) = res.content {
                pretty_assertions::assert_eq!(res.len(), l.len());
                for (a, b) in res.iter().zip(l.iter()) {
                    pretty_assertions::assert_eq!(a.as_u32().unwrap(), *b);
                }
            } else {
                panic!("wrong type for parsed object");
            }
        }
        Err(e) => {
            pretty_assertions::assert_eq!(res, Err(e));
        }
    }
}

#[test_case(&hex!("31 0a 02 03 01 00 01 02 03 01 00 00"), Ok(&[0x10001, 0x10000]) ; "set ok")]
#[test_case(&hex!("31 07 02 03 01 00 01 02 01"), Err(Err::Incomplete(Needed::new(1))) ; "incomplete")]
#[test_case(&hex!("30 0a 02 03 01 00 01 02 03 01 00 00"), Err(Err::Error(BerError::InvalidTag)) ; "invalid tag")]
#[test_case(&hex!("31 80 02 03 01 00 01 02 03 01 00 00 00 00"), Ok(&[0x10001, 0x10000]) ; "indefinite set")]
fn tc_ber_set_defined(i: &[u8], out: Result<&[u32], Err<BerError>>) {
    fn parser(i: &[u8]) -> BerResult<BerObject> {
        parse_ber_set_defined(map(
            tuple((parse_ber_integer, parse_ber_integer)),
            |(a, b)| vec![a, b],
        ))(i)
    }
    let res = parser(i);
    match out {
        Ok(l) => {
            let (rem, res) = res.expect("could not parse set");
            assert!(rem.is_empty());
            if let BerObjectContent::Set(res) = res.content {
                pretty_assertions::assert_eq!(res.len(), l.len());
                for (a, b) in res.iter().zip(l.iter()) {
                    pretty_assertions::assert_eq!(a.as_u32().unwrap(), *b);
                }
            } else {
                panic!("wrong type for parsed object");
            }
        }
        Err(e) => {
            pretty_assertions::assert_eq!(res, Err(e));
        }
    }
}
#[test]
fn empty_seq() {
    let data = &hex!("30 00");
    let (_, res) = parse_ber_sequence(data).expect("parsing empty sequence failed");
    assert!(res.as_sequence().unwrap().is_empty());
}

#[test]
fn struct01() {
    let bytes = [
        0x30, 0x0a, 0x02, 0x03, 0x01, 0x00, 0x01, 0x02, 0x03, 0x01, 0x00, 0x00,
    ];
    let empty = &b""[..];
    let expected = MyStruct {
        a: BerObject::from_int_slice(b"\x01\x00\x01"),
        b: BerObject::from_int_slice(b"\x01\x00\x00"),
    };
    let res = parse_struct01(&bytes);
    assert_eq!(res, Ok((empty, expected)));
}

#[test]
fn struct02() {
    let empty = &b""[..];
    let bytes = [
        0x30, 0x45, 0x31, 0x0b, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x46, 0x52,
        0x31, 0x13, 0x30, 0x11, 0x06, 0x03, 0x55, 0x04, 0x08, 0x0c, 0x0a, 0x53, 0x6f, 0x6d, 0x65,
        0x2d, 0x53, 0x74, 0x61, 0x74, 0x65, 0x31, 0x21, 0x30, 0x1f, 0x06, 0x03, 0x55, 0x04, 0x0a,
        0x16, 0x18, 0x49, 0x6e, 0x74, 0x65, 0x72, 0x6e, 0x65, 0x74, 0x20, 0x57, 0x69, 0x64, 0x67,
        0x69, 0x74, 0x73, 0x20, 0x50, 0x74, 0x79, 0x20, 0x4c, 0x74, 0x64,
    ];
    #[derive(Debug, PartialEq)]
    struct Attr<'a> {
        oid: Oid<'a>,
        val: BerObject<'a>,
    };
    #[derive(Debug, PartialEq)]
    struct Rdn<'a> {
        a: Attr<'a>,
    }
    #[derive(Debug, PartialEq)]
    struct Name<'a> {
        l: Vec<Rdn<'a>>,
    }
    let expected = Name {
        l: vec![
            Rdn {
                a: Attr {
                    oid: Oid::from(&[2, 5, 4, 6]).unwrap(), // countryName
                    val: BerObject::from_obj(BerObjectContent::PrintableString("FR")),
                },
            },
            Rdn {
                a: Attr {
                    oid: Oid::from(&[2, 5, 4, 8]).unwrap(), // stateOrProvinceName
                    val: BerObject::from_obj(BerObjectContent::UTF8String("Some-State")),
                },
            },
            Rdn {
                a: Attr {
                    oid: Oid::from(&[2, 5, 4, 10]).unwrap(), // organizationName
                    val: BerObject::from_obj(BerObjectContent::IA5String(
                        "Internet Widgits Pty Ltd",
                    )),
                },
            },
        ],
    };
    fn parse_directory_string(i: &[u8]) -> BerResult {
        alt!(
            i,
            parse_ber_utf8string | parse_ber_printablestring | parse_ber_ia5string
        )
    }
    fn parse_attr_type_and_value(i: &[u8]) -> BerResult<Attr> {
        fn clone_oid(x: BerObject) -> Result<Oid, BerError> {
            x.as_oid().map(|o| o.clone())
        }
        parse_der_struct!(
            i,
            o: map_res!(parse_ber_oid, clone_oid)
                >> s: parse_directory_string
                >> (Attr { oid: o, val: s })
        )
    };
    fn parse_rdn(i: &[u8]) -> BerResult<Rdn> {
        parse_der_struct!(i, a: parse_attr_type_and_value >> (Rdn { a }))
    }
    fn parse_name(i: &[u8]) -> BerResult<Name> {
        parse_der_struct!(i, l: many0!(complete!(parse_rdn)) >> (Name { l }))
    }
    let parsed = parse_name(&bytes).unwrap();
    assert_eq!(parsed, (empty, expected));
    //
    assert_eq!(parsed.1.l[0].a.val.as_str(), Ok("FR"));
    assert_eq!(parsed.1.l[1].a.val.as_str(), Ok("Some-State"));
    assert_eq!(parsed.1.l[2].a.val.as_str(), Ok("Internet Widgits Pty Ltd"));
}

#[test]
fn struct_with_garbage() {
    let bytes = [
        0x30, 0x0c, 0x02, 0x03, 0x01, 0x00, 0x01, 0x02, 0x03, 0x01, 0x00, 0x00, 0xff, 0xff,
    ];
    let empty = &b""[..];
    let expected = MyStruct {
        a: BerObject::from_int_slice(b"\x01\x00\x01"),
        b: BerObject::from_int_slice(b"\x01\x00\x00"),
    };
    assert_eq!(parse_struct01(&bytes), Ok((empty, expected)));
    assert_eq!(
        parse_struct01_complete(&bytes),
        Err(Err::Error(error_position!(&bytes[12..], ErrorKind::Eof)))
    );
}

#[test]
fn struct_verify_tag() {
    let bytes = [
        0x30, 0x0a, 0x02, 0x03, 0x01, 0x00, 0x01, 0x02, 0x03, 0x01, 0x00, 0x00,
    ];
    let empty = &b""[..];
    let expected = MyStruct {
        a: BerObject::from_int_slice(b"\x01\x00\x01"),
        b: BerObject::from_int_slice(b"\x01\x00\x00"),
    };
    let res = parse_struct04(&bytes, BerTag::Sequence);
    assert_eq!(res, Ok((empty, expected)));
    let res = parse_struct04(&bytes, BerTag::Set);
    assert_eq!(res, Err(Err::Error(BerError::InvalidTag)));
}

#[test_case(&hex!("a2 05 02 03 01 00 01"), Ok(0x10001) ; "tag ok")]
#[test_case(&hex!("a2 80 02 03 01 00 01 00 00"), Ok(0x10001) ; "indefinite tag ok")]
#[test_case(&hex!("a3 05 02 03 01 00 01"), Err(BerError::InvalidTag) ; "invalid tag")]
#[test_case(&hex!("22 05 02 03 01 00 01"), Err(BerError::InvalidClass) ; "invalid class")]
#[test_case(&hex!("82 05 02 03 01 00 01"), Err(BerError::ConstructExpected) ; "construct expected")]
fn tc_ber_tagged_explicit_g(i: &[u8], out: Result<u32, BerError>) {
    fn parse_int_explicit(i: &[u8]) -> BerResult<u32> {
        parse_ber_tagged_explicit_g(2, move |content, _hdr| {
            let (rem, obj) = parse_ber_integer(content)?;
            let value = obj.as_u32()?;
            Ok((rem, value))
        })(i)
    }
    let res = parse_int_explicit(i);
    match out {
        Ok(expected) => {
            pretty_assertions::assert_eq!(res, Ok((&b""[..], expected)));
        }
        Err(e) => {
            pretty_assertions::assert_eq!(res, Err(Err::Error(e)));
        }
    }
}

#[test]
fn tagged_explicit() {
    fn parse_int_explicit(i: &[u8]) -> BerResult<u32> {
        map_res!(
            i,
            parse_der_tagged!(EXPLICIT 2, parse_ber_integer),
            |x: BerObject| x.as_tagged()?.2.as_u32()
        )
    }
    fn parse_int_noexplicit(i: &[u8]) -> BerResult<u32> {
        map_res!(
            i,
            parse_der_tagged!(2, parse_ber_integer),
            |x: BerObject| x.as_tagged()?.2.as_u32()
        )
    }
    let bytes = &[0xa2, 0x05, 0x02, 0x03, 0x01, 0x00, 0x01];
    // EXPLICIT tagged value parsing
    let (rem, val) = parse_int_explicit(bytes).expect("Could not parse explicit int");
    assert!(rem.is_empty());
    assert_eq!(val, 0x10001);
    // omitting EXPLICIT keyword
    let a = parse_int_explicit(bytes);
    let b = parse_int_noexplicit(bytes);
    assert_eq!(a, b);
    // wrong tag
    assert_eq!(
        parse_der_tagged!(bytes as &[u8], 3, parse_ber_integer),
        Err(Err::Error(BerError::InvalidTag))
    );
    // wrong type
    assert_eq!(
        parse_der_tagged!(bytes as &[u8], 2, parse_ber_bool),
        Err(Err::Error(BerError::InvalidTag))
    );
}

#[test_case(&hex!("82 03 01 00 01"), Ok(0x10001) ; "tag ok")]
#[test_case(&hex!("83 03 01 00 01"), Err(BerError::InvalidTag) ; "invalid tag")]
fn tc_ber_tagged_implicit_g(i: &[u8], out: Result<u32, BerError>) {
    fn parse_int_implicit(i: &[u8]) -> BerResult<u32> {
        parse_ber_tagged_implicit_g(2, |content, hdr, depth| {
            let (rem, obj) = parse_ber_content(BerTag::Integer)(content, &hdr, depth)?;
            let value = obj.as_u32()?;
            Ok((rem, value))
        })(i)
    }
    let res = parse_int_implicit(i);
    match out {
        Ok(expected) => {
            pretty_assertions::assert_eq!(res, Ok((&b""[..], expected)));
        }
        Err(e) => {
            pretty_assertions::assert_eq!(res, Err(Err::Error(e)));
        }
    }
}

#[test]
fn tagged_implicit() {
    fn parse_int_implicit(i: &[u8]) -> BerResult<u32> {
        map_res!(
            i,
            parse_der_tagged!(IMPLICIT 2, BerTag::Integer),
            |x: BerObject| x.as_u32()
        )
    }
    let bytes = &[0x82, 0x03, 0x01, 0x00, 0x01];
    // IMPLICIT tagged value parsing
    let (rem, val) = parse_int_implicit(bytes).expect("could not parse implicit int");
    assert!(rem.is_empty());
    assert_eq!(val, 0x10001);
    // wrong tag
    assert_eq!(
        parse_der_tagged!(bytes as &[u8], IMPLICIT 3, BerTag::Integer),
        Err(Err::Error(BerError::InvalidTag))
    );
}

#[test]
fn application() {
    #[derive(Debug, PartialEq)]
    struct SimpleStruct {
        a: u32,
    };
    fn parse_app01(i: &[u8]) -> BerResult<SimpleStruct> {
        parse_der_application!(
            i,
            APPLICATION 2,
            a: map_res!(parse_ber_integer,|x: BerObject| x.as_u32()) >>
            ( SimpleStruct{ a } )
        )
    }
    let bytes = &[0x62, 0x05, 0x02, 0x03, 0x01, 0x00, 0x01];
    let (rem, app) = parse_app01(bytes).expect("could not parse application");
    assert!(rem.is_empty());
    assert_eq!(app, SimpleStruct { a: 0x10001 });
}

#[test]
#[ignore = "not yet implemented"]
fn ber_constructed_string() {
    // this encoding is equivalent to "04 05 01 AB 23 7F CA"
    let data = &hex!(
        "
        24 80
            04 02 01 ab
            04 02 23 7f
            04 01 ca
        00 00"
    );
    let _ = parse_ber_octetstring(data).expect("parsing failed");
}
