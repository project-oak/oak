use std::collections::BTreeMap;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Generics, Meta};
use crate::Trait;

pub struct PartialOrdStructHandler;

impl TraitHandler for PartialOrdStructHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_flag: true,
            enable_bound: true,
            rank: 0,
            enable_rank: false,
        }
        .from_partial_ord_meta(meta);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut comparer_tokens = TokenStream::new();

        if let Data::Struct(data) = &ast.data {
            let mut field_attributes = BTreeMap::new();
            let mut field_names = BTreeMap::new();

            for (index, field) in data.fields.iter().enumerate() {
                let field_attribute = FieldAttributeBuilder {
                    enable_ignore: true,
                    enable_impl: true,
                    rank: isize::min_value() + index as isize,
                    enable_rank: true,
                }
                .from_attributes(&field.attrs, traits);

                if field_attribute.ignore {
                    continue;
                }

                let rank = field_attribute.rank;

                if field_attributes.contains_key(&rank) {
                    panic::reuse_a_rank(rank);
                }

                let field_name = if let Some(ident) = field.ident.as_ref() {
                    ident.to_string()
                } else {
                    format!("{}", index)
                };

                field_attributes.insert(rank, field_attribute);
                field_names.insert(rank, field_name);
            }

            for (index, field_attribute) in field_attributes {
                let field_name = field_names.get(&index).unwrap();

                let compare_trait = field_attribute.compare_trait;
                let compare_method = field_attribute.compare_method;

                match compare_trait {
                    Some(compare_trait) => {
                        let compare_method = compare_method.unwrap();

                        let statement = format!("match {compare_trait}::{compare_method}(&self.{field_name}, &other.{field_name}) {{ Some(core::cmp::Ordering::Equal) => (), Some(core::cmp::Ordering::Greater) => {{ return Some(core::cmp::Ordering::Greater); }}, Some(core::cmp::Ordering::Less) => {{ return Some(core::cmp::Ordering::Less); }}, None => {{ return None; }} }}", compare_trait = compare_trait, compare_method = compare_method, field_name = field_name);

                        comparer_tokens.extend(TokenStream::from_str(&statement).unwrap());
                    }
                    None => {
                        match compare_method {
                            Some(compare_method) => {
                                let statement = format!("match {compare_method}(&self.{field_name}, &other.{field_name}) {{ Some(core::cmp::Ordering::Equal) => (), Some(core::cmp::Ordering::Greater) => {{ return Some(core::cmp::Ordering::Greater); }}, Some(core::cmp::Ordering::Less) => {{ return Some(core::cmp::Ordering::Less); }}, None => {{ return None; }} }}", compare_method = compare_method, field_name = field_name);

                                comparer_tokens.extend(TokenStream::from_str(&statement).unwrap());
                            }
                            None => {
                                let statement = format!("match core::cmp::PartialOrd::partial_cmp(&self.{field_name}, &other.{field_name}) {{ Some(core::cmp::Ordering::Equal) => (), Some(core::cmp::Ordering::Greater) => {{ return Some(core::cmp::Ordering::Greater); }}, Some(core::cmp::Ordering::Less) => {{ return Some(core::cmp::Ordering::Less); }}, None => {{ return None; }} }}", field_name = field_name);

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
            impl #impl_generics core::cmp::PartialOrd for #ident #ty_generics #where_clause {
                #[inline]
                fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                    #comparer_tokens

                    Some(core::cmp::Ordering::Equal)
                }
            }
        };

        tokens.extend(compare_impl);
    }
}
