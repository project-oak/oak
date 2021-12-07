extern crate proc_macro2;
extern crate proc_quote;

use proc_macro2::{Ident, Span, TokenStream};
use proc_quote::{quote, TokenStreamExt};

struct X;

impl quote::ToTokens for X {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Ident::new("X", Span::call_site()));
    }
}

#[test]
fn test_repetition_simple() {
    let primes = &[X, X, X, X];

    assert_eq!("X X X X", quote!(#(#primes)*).to_string());

    assert_eq!("X , X , X , X ,", quote!(#(#primes,)*).to_string());

    assert_eq!("X , X , X , X", quote!(#(#primes),*).to_string());
}

#[test]
fn test_repetition_two_vars() {
    let foo = vec!["a", "b"];
    let bar = vec![true, false];

    let tokens = quote! {
        #(#foo: #bar),*
    };

    let expected = r#""a" : true , "b" : false"#;
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_repetition_nested() {
    let nested = vec![vec!['a', 'b', 'c'], vec!['x', 'y', 'z']];

    let tokens = quote! {
        #(
            #(#nested)*
        ),*
    };

    let expected = "'a' 'b' 'c' , 'x' 'y' 'z'";
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_var_name_conflict() {
    // The implementation of `#(...),*` uses the variable `__i` but it should be
    // fine, if a little confusing when debugging.
    let __i = vec!['a', 'b'];
    let tokens = quote! {
        #(#__i),*
    };
    let expected = "'a' , 'b'";
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_repetition_same_iter_twice() {
    let a = 1..=3;
    let b = quote! {
        #(#a #a)*
    };
    assert_eq!("1i32 1i32 2i32 2i32 3i32 3i32", b.to_string());
}

#[test]
fn test_repetition_iterators() {
    let a = vec!["a", "b", "c"].into_iter();
    let b = 2..6;
    let c = [5, 6, 7].into_iter().map(|_| X);
    let q = quote! {
        #(#a #b #c)*
    };
    assert_eq!("\"a\" 2i32 X \"b\" 3i32 X \"c\" 4i32 X", q.to_string());
}

#[test]
fn test_repetition_slices() {
    let a = vec!["a", "b", "c"];
    let b = &[2, 3, 4, 5];
    let c = [5, 6, 7];

    let q = quote! {
        #(#a #b #c)*
    };
    assert_eq!(
        "\"a\" 2i32 5i32 \"b\" 3i32 6i32 \"c\" 4i32 7i32",
        q.to_string()
    );
}

#[test]
fn test_repetition_totokens() {
    let i = 1..3; // Iterator just to avoid infinite loop
    let a = 5;
    let b = "a";
    let c = X;

    let q = quote! {
        #(#i #a #b #c)*
    };
    assert_eq!("1i32 5i32 \"a\" X 2i32 5i32 \"a\" X", q.to_string());
}

#[test]
fn test_repetition_without_consuming() {
    // The following types should not be consumed by `quote!`
    let a = [1, 2, 3];
    let b = vec!['a', 'b', 'c'];
    let c = 5.0;

    let q1 = quote! {
        #(#a #b #c)* #(#a #b #c)* // Usable in two different patterns
    };
    let q2 = quote! {
        #(#a #b #c)* // Usable in a different `quote!`
    };
    let d = (a[0], b[0], c); // Still usable in the following code

    assert_eq!(
        "1i32 'a' 5f64 2i32 'b' 5f64 3i32 'c' 5f64 1i32 'a' 5f64 2i32 'b' 5f64 3i32 'c' 5f64",
        q1.to_string()
    );
    assert_eq!("1i32 'a' 5f64 2i32 'b' 5f64 3i32 'c' 5f64", q2.to_string());
    assert_eq!(1, d.0);
    assert_eq!('a', d.1);
    assert_eq!(5.0, d.2);
}

#[test]
fn test_repetition_trait_name_collision() {
    trait Repeat {}
    impl Repeat for X {}

    let a = 0..3; // Avoid infinite loop
    let x = X;

    let q = quote! {
        #(#a #x)*
    };

    assert_eq!("0i32 X 1i32 X 2i32 X", q.to_string());
}

#[test]
#[ignore] // TODO(#7) trait fn collision
fn test_repetition_trait_fn_collision() {
    unimplemented!("doesn't compile")

    // trait Repeat {
    //     fn __proc_quote__as_repeat(self) -> !;
    // }
    // impl Repeat for X {
    //     fn __proc_quote__as_repeat(self) -> ! { panic!("Wrong trait called.") }
    // }

    // let a = 0..3; // Avoid infinite loop
    // let x = X;

    // let q = quote! {
    //     #(#a #x)*
    // };

    // assert_eq!("0i32 X 1i32 X 2i32 X", q.to_string());
}

#[test]
#[ignore] // TODO(#7) struct method name collision
fn test_repetition_impl_fn_collision() {
    unimplemented!("doesn't compile")

    // struct R;
    // impl R {
    //     fn __proc_quote__as_repeat(self) -> ! { panic!("Wrong trait called.") }
    // }
    // impl quote::ToTokens for R {
    //     fn to_tokens(&self, tokens: &mut TokenStream) {
    //         tokens.append(Ident::new("X", Span::call_site()));
    //     }
    // }

    // let a = 0..3; // Avoid infinite loop
    // let r = R;

    // let q = quote! {
    //     #(#a #r)*
    // };

    // assert_eq!("0i32 X 1i32 X 2i32 X", q.to_string());
}
