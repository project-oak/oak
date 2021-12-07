mod models;

use super::TraitHandler;

use crate::proc_macro2::TokenStream;
use crate::syn::{DeriveInput, Generics, Meta};
use crate::Trait;

use models::TypeAttributeBuilder;

pub struct CopyHandler;

impl TraitHandler for CopyHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        _traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_bound: true,
        }
        .from_copy_meta(meta);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let ident = &ast.ident;

        let mut generics_cloned: Generics = ast.generics.clone();

        let where_clause = generics_cloned.make_where_clause();

        for where_predicate in bound {
            where_clause.predicates.push(where_predicate);
        }

        let (impl_generics, ty_generics, where_clause) = generics_cloned.split_for_impl();

        let copy_impl = quote! {
            impl #impl_generics core::marker::Copy for #ident #ty_generics #where_clause {
            }
        };

        tokens.extend(copy_impl);
    }
}
