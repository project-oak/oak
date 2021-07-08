#![allow(deprecated)]

use der_parser::ber::{parse_ber_integer, BerObject};
use der_parser::der::{parse_der_enum, parse_der_integer};
use der_parser::error::{BerResult, DerResult};
use der_parser::*;
use nom::map_res;

// Do not import nom, to check types and re-exports

// all following functions are declared to check if macros from
// der-parser can be used without importing nom or rusticata_macros

#[derive(Debug, PartialEq)]
struct MyStruct<'a> {
    a: BerObject<'a>,
    b: BerObject<'a>,
}

#[allow(dead_code)]
fn parse_seq_m(i: &[u8]) -> DerResult {
    parse_der_sequence_defined_m! {
        i,
        parse_der_integer >>
        parse_der_integer
    }
}

#[allow(dead_code)]
fn parse_set_m(i: &[u8]) -> DerResult {
    parse_der_set_defined_m! {
        i,
        parse_der_integer >>
        parse_der_integer
    }
}

#[allow(dead_code)]
fn parse_seq(i: &[u8]) -> DerResult {
    parse_der_sequence_defined! {
        i,
        parse_der_integer >>
        parse_der_integer
    }
}

#[allow(dead_code)]
fn parse_set(i: &[u8]) -> DerResult {
    parse_der_set_defined! {
        i,
        parse_der_integer >>
        parse_der_integer
    }
}

#[allow(dead_code)]
fn parse_seq_of_int(i: &[u8]) -> DerResult {
    parse_der_sequence_of!(i, parse_der_integer)
}

#[allow(dead_code)]
fn parse_set_of_int(i: &[u8]) -> DerResult {
    parse_der_set_of!(i, parse_der_integer)
}

#[allow(dead_code)]
fn parse_optional_enum(i: &[u8]) -> BerResult {
    parse_der_optional!(i, parse_der_enum)
}

#[allow(dead_code)]
fn parse_struct01(i: &[u8]) -> BerResult<MyStruct> {
    parse_der_struct!(
        i,
        a: parse_ber_integer >> b: parse_ber_integer >> (MyStruct { a, b })
    )
}

#[allow(dead_code)]
fn parse_tagged_int(i: &[u8]) -> BerResult {
    parse_der_tagged!(i, EXPLICIT 2, parse_ber_integer)
}

#[derive(Debug, PartialEq)]
struct SimpleStruct {
    a: u32,
}

#[allow(dead_code)]
fn parse_app_int(i: &[u8]) -> BerResult<SimpleStruct> {
    parse_der_application!(
        i,
        APPLICATION 2,
        a: map_res!(parse_ber_integer,|x: BerObject| x.as_u32()) >>
        ( SimpleStruct{ a } )
    )
}

#[rustfmt::skip::macros(oid)]
#[test]
fn oid_macro() {
    let abs = oid!(1.2.44.233.0.124_982_9_348248912829838230928);
    assert!(!abs.relative);
    if cfg!(feature = "bigint") {
        assert_eq!(abs.to_string(), "1.2.44.233.0.1249829348248912829838230928");
    } else {
        assert_eq!(
            abs.to_string(),
            "2a 2c 81 69 00 c0 ce d6 d1 ba fd 8e c7 e5 dc ee 8b 10"
        );
    }

    let rel = oid!(rel 1.2.44.233);
    assert!(rel.relative);
    assert_eq!(rel.to_id_string(), "1.2.44.233");
    assert_eq!(format!("{:?}", &rel), "OID(rel. 1.2.44.233)")
}

#[test]
fn oid_macro_edge_cases() {
    let undef = oid!(0);
    assert_eq!(undef.bytes(), [0].as_ref());

    let two = oid!(1.2);
    assert_eq!(two.bytes(), [40 + 2].as_ref());

    let spacing = oid!(5.2);
    assert_eq!(spacing.bytes(), [5 * 40 + 2].as_ref());
}
