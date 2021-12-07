use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Generics, Meta};
use crate::Trait;

pub struct PartialEqStructHandler;

impl TraitHandler for PartialEqStructHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_flag: true,
            enable_bound: true,
        }
        .from_partial_eq_meta(meta);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut comparer_tokens = TokenStream::new();

        if let Data::Struct(data) = &ast.data {
            for (index, field) in data.fields.iter().enumerate() {
                let field_attribute = FieldAttributeBuilder {
                    enable_ignore: true,
                    enable_impl: true,
                }
                .from_attributes(&field.attrs, traits);

                if field_attribute.ignore {
                    continue;
                }

                let compare_trait = field_attribute.compare_trait;
                let compare_method = field_attribute.compare_method;

                let field_name = if let Some(ident) = field.ident.as_ref() {
                    ident.to_string()
                } else {
                    format!("{}", index)
                };

                match compare_trait {
                    Some(compare_trait) => {
                        let compare_method = compare_method.unwrap();

                        let statement = format!("if !{compare_trait}::{compare_method}(&self.{field_name}, &other.{field_name}) {{ return false }}", compare_trait = compare_trait, compare_method = compare_method, field_name = field_name);

                        comparer_tokens.extend(TokenStream::from_str(&statement).unwrap());
                    }
                    None => {
                        match compare_method {
                            Some(compare_method) => {
                                let statement = format!("if !{compare_method}(&self.{field_name}, &other.{field_name}) {{ return false; }}", compare_method = compare_method, field_name = field_name);

                                comparer_tokens.extend(TokenStream::from_str(&statement).unwrap());
                            }
                            None => {
                                let statement = format!("if core::cmp::PartialEq::ne(&self.{field_name}, &other.{field_name}) {{ return false; }}", field_name = field_name);

                                comparer_tokens.extend(TokenStream::from_str(&statement).unwrap());
                            }
                        }
                    }
                }
            }
        }

        let ident = &ast.ident;

        let mut generics_cloned: Generics = ast.generics.clone();

        let where_clause = generics_cloned.make_where_clause();

        for where_predicate in bound {
            where_clause.predicates.push(where_predicate);
        }

        let (impl_generics, ty_generics, where_clause) = generics_cloned.split_for_impl();

        let compare_impl = quote! {
            impl #impl_generics core::cmp::PartialEq for #ident #ty_generics #where_clause {
                #[inline]
                fn eq(&self, other: &Self) -> bool {
                    #comparer_tokens

                    true
                }
            }
        };

        tokens.extend(compare_impl);
    }
}
