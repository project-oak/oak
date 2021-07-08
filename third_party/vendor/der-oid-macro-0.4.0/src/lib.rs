extern crate proc_macro;

use proc_macro::TokenStream;
fn parse_arg(arg: &str) -> (bool, bool, Vec<&str>) {
    use nom::{
        bytes::complete::{tag, take_while},
        call,
        character::complete::{char, digit1},
        combinator::{map, opt, recognize, verify},
        error::{ErrorKind, ParseError},
        exact,
        multi::separated_list1,
        sequence::{delimited, terminated, tuple},
        IResult,
    };

    fn uint<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
        verify(recognize(separated_list1(char('_'), digit1)), |s: &str| {
            s.len() == 1 || !s.starts_with('0')
        })(i)
    }

    fn ws<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
        take_while(|c| c == ' ')(i)
    }

    fn ws_dot_ws<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, char, E> {
        delimited(ws, char('.'), ws)(i)
    }

    fn root<'a, E: ParseError<&'a str>>(
        i: &'a str,
    ) -> IResult<&'a str, (bool, bool, Vec<&'a str>), E> {
        tuple((
            map(opt(terminated(tag("raw "), ws)), |x| x.is_some()),
            map(opt(terminated(tag("rel "), ws)), |x| x.is_some()),
            separated_list1(ws_dot_ws, uint),
        ))(i)
    }

    exact!(arg.trim(), call!(root::<(&str, ErrorKind)>))
        .expect("could not parse oid")
        .1
}

fn encode_components(components: &[num_bigint::BigUint], relative: bool) -> Vec<u8> {
    use num_traits::cast::ToPrimitive;

    let mut enc = Vec::new();
    let mut dec = components;
    if !relative {
        if dec.len() < 2 {
            if dec.len() == 1 && dec[0] == 0u8.into() {
                return vec![0];
            }
            panic!("Need at least two components for non-relative oid");
        }
        if dec[0] >= 7u8.into() || dec[1] >= 40u8.into() {
            panic!("First components are too big");
        }
        enc.push(dec[0].to_u8().unwrap() * 40 + dec[1].to_u8().unwrap());
        dec = &dec[2..];
    }

    for int in dec.iter() {
        let mut bytes = int.to_bytes_be();
        if bytes[0] == 0 {
            enc.push(0u8);
            continue;
        }
        let total_bits = (8 - bytes[0].leading_zeros()) as usize + (bytes.len() - 1) * 8;
        let octects_needed = ((total_bits + 6) / 7).max(1);
        enc.resize_with(enc.len() + octects_needed, Default::default);

        let mut pos = enc.len() - 1;
        let mut extra = 0u8;
        let mut extra_size = 0u8;
        bytes.reverse();
        let mut bytes_stored = 0;
        for byte in bytes.into_iter() {
            if extra_size == 7 {
                // there a seven bits in extra
                enc[pos] = extra | (1 << 7);
                bytes_stored += 1;
                pos -= 1;
                extra = 0;
                extra_size = 0;
            }
            // make space for the extra bits
            enc[pos] = (byte << extra_size) | extra | (1 << 7);
            bytes_stored += 1;
            if pos > 0 {
                pos -= 1;
                extra_size += 1;
                extra = byte >> (8 - extra_size);
            }
        }
        let last = enc.len() - 1;
        if bytes_stored != octects_needed {
            let first = last + 1 - octects_needed;
            enc[first] = extra | (1 << 7);
        }
        enc[last] ^= 1 << 7;
    }
    enc
}

#[proc_macro]
pub fn oid(item: TokenStream) -> TokenStream {
    let arg = item.to_string();
    let (raw, relative, int_strings) = parse_arg(&arg);
    let ints: Vec<num_bigint::BigUint> = int_strings
        .into_iter()
        .map(|s| s.parse().unwrap())
        .collect();
    let enc = encode_components(&ints, relative);

    let mut s = String::with_capacity(2 + 6 * enc.len());
    s.push('[');
    for byte in enc.iter() {
        s.insert_str(s.len(), &format!("0x{:02x}, ", byte));
    }
    s.push(']');

    let code = if raw {
        s
    } else if relative {
        format!(
            "der_parser::oid::Oid::new_relative(std::borrow::Cow::Borrowed(&{}))",
            s
        )
    } else {
        format!(
            "der_parser::oid::Oid::new(std::borrow::Cow::Borrowed(&{}))",
            s
        )
    };
    code.parse().unwrap()
}
