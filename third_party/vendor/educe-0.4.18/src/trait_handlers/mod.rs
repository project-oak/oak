#![cfg_attr(not(feature = "default"), allow(dead_code))]

#[cfg(feature = "Clone")]
pub mod clone;
#[cfg(feature = "Copy")]
pub mod copy;
#[cfg(feature = "Debug")]
pub mod debug;
#[cfg(feature = "Default")]
pub mod default;
#[cfg(feature = "Deref")]
pub mod deref;
#[cfg(feature = "DerefMut")]
pub mod deref_mut;
#[cfg(feature = "Eq")]
pub mod eq;
#[cfg(feature = "Hash")]
pub mod hash;
#[cfg(feature = "Ord")]
pub mod ord;
#[cfg(feature = "PartialEq")]
pub mod partial_eq;
#[cfg(feature = "PartialOrd")]
pub mod partial_ord;

use std::str::FromStr;

use crate::proc_macro2::TokenStream;
use crate::quote::ToTokens;
use crate::syn::{
    self, punctuated::Punctuated, token::Comma, DeriveInput, Expr, GenericParam, LitStr, Meta,
    Path, WhereClause, WherePredicate,
};
use crate::Trait;

pub trait TraitHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    );
}

#[inline]
pub fn create_path_from_lit_str(s: &LitStr) -> Option<Path> {
    let s = s.value();

    let s = s.trim();

    if s.is_empty() {
        None
    } else {
        let tokens = TokenStream::from_str(s).unwrap();

        Some(syn::parse2(tokens).unwrap())
    }
}

#[inline]
pub fn create_path_string_from_lit_str(s: &LitStr) -> Option<String> {
    create_path_from_lit_str(s).map(|path| path.into_token_stream().to_string().replace(" ", ""))
}

#[inline]
pub fn create_expr_from_lit_str(s: &LitStr) -> Option<Expr> {
    let s = s.value();

    let s = s.trim();

    if s.is_empty() {
        None
    } else {
        let tokens = TokenStream::from_str(s).unwrap();

        Some(syn::parse2(tokens).unwrap())
    }
}

#[inline]
pub fn create_expr_string_from_lit_str(s: &LitStr) -> Option<String> {
    create_expr_from_lit_str(s).map(|expr| expr.into_token_stream().to_string().replace(" ", ""))
}

#[inline]
pub fn create_where_predicates_from_lit_str(
    s: &LitStr,
) -> Option<Punctuated<WherePredicate, Comma>> {
    let s = s.value();

    let s = s.trim();

    if s.is_empty() {
        None
    } else {
        let s = format!("where {}", s);

        let tokens = TokenStream::from_str(&s).unwrap();

        let where_clause: WhereClause = syn::parse2(tokens).unwrap();

        Some(where_clause.predicates)
    }
}

#[inline]
pub fn create_where_predicates_from_generic_parameters(
    p: &Punctuated<GenericParam, Comma>,
    bound_trait: &Path,
) -> Punctuated<WherePredicate, Comma> {
    let mut where_predicates = Punctuated::new();

    for param in p.iter() {
        if let GenericParam::Type(typ) = param {
            let ident = &typ.ident;

            where_predicates.push(syn::parse2(quote! { #ident: #bound_trait }).unwrap());
        }
    }

    where_predicates
}
