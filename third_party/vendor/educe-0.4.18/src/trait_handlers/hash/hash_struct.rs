use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Generics, Meta};
use crate::Trait;

pub struct HashStructHandler;

impl TraitHandler for HashStructHandler {
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
        .from_hash_meta(meta);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut hasher_tokens = TokenStream::new();

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

                let hash_trait = field_attribute.hash_trait;
                let hash_method = field_attribute.hash_method;

                let field_name = if let Some(ident) = field.ident.as_ref() {
                    ident.to_string()
                } else {
                    format!("{}", index)
                };

                match hash_trait {
                    Some(hash_trait) => {
                        let hash_method = hash_method.unwrap();

                        let statement = format!(
                            "{hash_trait}::{hash_method}(&self.{field_name}, state);",
                            hash_trait = hash_trait,
                            hash_method = hash_method,
                            field_name = field_name
                        );

                        hasher_tokens.extend(TokenStream::from_str(&statement).unwrap());
                    }
                    None => {
                        match hash_method {
                            Some(hash_method) => {
                                let statement = format!(
                                    "{hash_method}(&self.{field_name}, state);",
                                    hash_method = hash_method,
                                    field_name = field_name
                                );

                                hasher_tokens.extend(TokenStream::from_str(&statement).unwrap());
                            }
                            None => {
                                let statement = format!(
                                    "core::hash::Hash::hash(&self.{field_name}, state);",
                                    field_name = field_name
                                );

                                hasher_tokens.extend(TokenStream::from_str(&statement).unwrap());
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

        let hash_impl = quote! {
            impl #impl_generics core::hash::Hash for #ident #ty_generics #where_clause {
                #[inline]
                fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                    #hasher_tokens
                }
            }
        };

        tokens.extend(hash_impl);
    }
}
