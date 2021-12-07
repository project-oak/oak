mod models;

use super::TraitHandler;

use crate::proc_macro2::TokenStream;
use crate::syn::{DeriveInput, Generics, Meta};
use crate::Trait;

use models::TypeAttributeBuilder;

pub struct EqHandler;

impl TraitHandler for EqHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        _traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_bound: true,
        }
        .from_eq_meta(meta);

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

        let compare_impl = quote! {
            impl #impl_generics core::cmp::Eq for #ident #ty_generics #where_clause {
            }
        };

        tokens.extend(compare_impl);
    }
}
