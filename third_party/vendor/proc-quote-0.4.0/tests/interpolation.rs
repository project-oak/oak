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
fn test_ident() {
    let foo = Ident::new("Foo", Span::call_site());
    let bar = Ident::new(&format!("Bar{}", 7), Span::call_site());
    let tokens = quote!(struct #foo; enum #bar {});
    let expected = "struct Foo ; enum Bar7 { }";
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_duplicate() {
    let ch = 'x';

    let tokens = quote!(#ch #ch);

    let expected = "'x' 'x'";
    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_substitution() {
    let x = X;
    let tokens = quote!(#x <#x> (#x) [#x] {#x});

    let expected = "X < X > (X) [X] { X }";

    assert_eq!(expected, tokens.to_string());
}

#[test]
fn test_advanced() {
    let generics = quote!( <'a, T> );

    let where_clause = quote!( where T: Serialize );

    let field_ty = quote!(String);

    let item_ty = quote!(Cow<'a, str>);

    let path = quote!(SomeTrait::serialize_with);

    let value = quote!(self.x);

    let tokens = quote! {
        struct SerializeWith #generics #where_clause {
            value: &'a #field_ty,
            phantom: ::std::marker::PhantomData<#item_ty>,
        }

        impl #generics ::serde::Serialize for SerializeWith #generics #where_clause {
            fn serialize<S>(&self, s: &mut S) -> Result<(), S::Error>
                where S: ::serde::Serializer
            {
                #path(self.value, s)
            }
        }

        SerializeWith {
            value: #value,
            phantom: ::std::marker::PhantomData::<#item_ty>,
        }
    };

    let expected = concat!(
        "struct SerializeWith < 'a , T > where T : Serialize { ",
        "value : & 'a String , ",
        "phantom : :: std :: marker :: PhantomData <Cow < 'a , str > >, ",
        "} ",
        "impl < 'a , T > :: serde :: Serialize for SerializeWith < 'a , T > where T : Serialize { ",
        "fn serialize < S > (& self , s : & mut S) -> Result < () , S :: Error > ",
        "where S : :: serde :: Serializer ",
        "{ ",
        "SomeTrait :: serialize_with (self . value , s) ",
        "} ",
        "} ",
        "SerializeWith { ",
        "value : self . x , ",
        "phantom : :: std :: marker :: PhantomData ::<Cow < 'a , str > >, ",
        "}"
    );

    assert_eq!(expected, tokens.to_string());
}
