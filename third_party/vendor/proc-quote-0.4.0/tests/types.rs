extern crate proc_macro2;
extern crate proc_quote;

use std::borrow::Cow;

use proc_macro2::{Ident, Span};
use proc_quote::quote;

#[test]
fn test_integer() {
    let ii8 = -1i8;
    let ii16 = -1i16;
    let ii32 = -1i32;
    let ii64 = -1i64;
    let iisize = -1isize;
    let uu8 = 1u8;
    let uu16 = 1u16;
    let uu32 = 1u32;
    let uu64 = 1u64;
    let uusize = 1usize;

    let tokens = quote! {
        #ii8 #ii16 #ii32 #ii64 #iisize
        #uu8 #uu16 #uu32 #uu64 #uusize
    };
    let expected = "- 1i8 - 1i16 - 1i32 - 1i64 - 1isize 1u8 1u16 1u32 1u64 1usize";
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_floating() {
    let e32 = 2.345f32;

    let e64 = 2.345f64;

    let tokens = quote! {
        #e32
        #e64
    };
    let expected = concat!("2.345f32 2.345f64");
    assert_eq!(expected, tokens.to_string());
}

#[cfg(integer128)]
#[test]
fn test_integer128() {
    let ii128 = -1i128;
    let uu128 = 1u128;

    let tokens = quote! {
        #ii128 #uu128
    };
    let expected = "-1i128 1u128";
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_char() {
    let zero = '\0';
    let pound = '#';
    let quote = '"';
    let apost = '\'';
    let newline = '\n';
    // ISSUE #19 https://github.com/Goncalerta/proc-quote/issues/19
    //let heart = '\u{2764}';

    let tokens = quote! {
        #zero #pound #quote #apost #newline
    };
    let expected = r#"'\u{0}' '#' '"' '\'' '\n'"#;
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_str() {
    let s = "\0 a 'b \" c";
    let tokens = quote!(#s);
    let expected = r#""\u{0} a 'b \" c""#;
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_string() {
    let s = "\0 a 'b \" c".to_string();
    let tokens = quote!(#s);
    let expected = r#""\u{0} a 'b \" c""#;
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_box_str() {
    let b = "str".to_owned().into_boxed_str();
    let tokens = quote!( #b );
    assert_eq!("\"str\"", tokens.to_string());
}

#[test]
fn test_cow() {
    let owned: Cow<Ident> = Cow::Owned(Ident::new("owned", Span::call_site()));

    let ident = Ident::new("borrowed", Span::call_site());
    let borrowed = Cow::Borrowed(&ident);

    let tokens = quote!( #owned #borrowed );
    assert_eq!("owned borrowed", tokens.to_string());
}
