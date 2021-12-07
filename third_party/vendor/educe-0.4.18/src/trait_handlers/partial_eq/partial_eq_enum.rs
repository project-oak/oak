use std::fmt::Write;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Fields, Generics, Meta};
use crate::Trait;

pub struct PartialEqEnumHandler;

impl TraitHandler for PartialEqEnumHandler {
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

        let enum_name = ast.ident.to_string();

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut comparer_tokens = TokenStream::new();

        let mut match_tokens = String::from("match self {");

        if let Data::Enum(data) = &ast.data {
            for variant in data.variants.iter() {
                let _ = TypeAttributeBuilder {
                    enable_flag: false,
                    enable_bound: false,
                }
                .from_attributes(&variant.attrs, traits);

                let variant_ident = variant.ident.to_string();

                match &variant.fields {
                    Fields::Unit => {
                        // TODO Unit
                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ if let {enum_name}::{variant_ident} = other {{ }} else {{ return false; }} }}", enum_name = enum_name, variant_ident = variant_ident)).unwrap();
                    }
                    Fields::Named(fields) => {
                        // TODO Struct
                        let mut pattern_tokens = String::new();
                        let mut pattern_2_tokens = String::new();
                        let mut block_tokens = String::new();

                        let mut field_attributes = Vec::new();
                        let mut field_names = Vec::new();

                        for field in fields.named.iter() {
                            let field_attribute = FieldAttributeBuilder {
                                enable_ignore: true,
                                enable_impl: true,
                            }
                            .from_attributes(&field.attrs, traits);

                            let field_name = field.ident.as_ref().unwrap().to_string();

                            if field_attribute.ignore {
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}: _,",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_2_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}: _,",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                continue;
                            }

                            pattern_tokens
                                .write_fmt(format_args!("{field_name},", field_name = field_name))
                                .unwrap();
                            pattern_2_tokens
                                .write_fmt(format_args!(
                                    "{field_name}: ___{field_name},",
                                    field_name = field_name
                                ))
                                .unwrap();

                            field_attributes.push(field_attribute);
                            field_names.push(field_name);
                        }

                        for (index, field_attribute) in field_attributes.into_iter().enumerate() {
                            let field_name = &field_names[index];

                            let compare_trait = field_attribute.compare_trait;
                            let compare_method = field_attribute.compare_method;

                            match compare_trait {
                                Some(compare_trait) => {
                                    let compare_method = compare_method.unwrap();

                                    block_tokens.write_fmt(format_args!("if !{compare_trait}::{compare_method}({field_name}, ___{field_name}) {{ return false; }}", compare_trait = compare_trait, compare_method = compare_method, field_name = field_name)).unwrap();
                                }
                                None => {
                                    match compare_method {
                                        Some(compare_method) => {
                                            block_tokens.write_fmt(format_args!("if !{compare_method}({field_name}, ___{field_name}) {{ return false; }}", compare_method = compare_method, field_name = field_name)).unwrap();
                                        }
                                        None => {
                                            block_tokens.write_fmt(format_args!("if core::cmp::PartialEq::ne({field_name}, ___{field_name}) {{ return false; }}", field_name = field_name)).unwrap();
                                        }
                                    }
                                }
                            }
                        }

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}{{ {pattern_tokens} }} => {{ if let {enum_name}::{variant_ident} {{ {pattern_2_tokens} }} = other {{ {block_tokens} }} else {{ return false; }} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, pattern_2_tokens = pattern_2_tokens, block_tokens = block_tokens)).unwrap();
                    }
                    Fields::Unnamed(fields) => {
                        // TODO Tuple
                        let mut pattern_tokens = String::new();
                        let mut pattern_2_tokens = String::new();
                        let mut block_tokens = String::new();

                        let mut field_attributes = Vec::new();
                        let mut field_names = Vec::new();

                        for (index, field) in fields.unnamed.iter().enumerate() {
                            let field_attribute = FieldAttributeBuilder {
                                enable_ignore: true,
                                enable_impl: true,
                            }
                            .from_attributes(&field.attrs, traits);

                            let field_name = format!("{}", index);

                            if field_attribute.ignore {
                                pattern_tokens.push_str("_,");
                                pattern_2_tokens.push_str("_,");
                                continue;
                            }

                            pattern_tokens
                                .write_fmt(format_args!("_{field_name},", field_name = field_name))
                                .unwrap();
                            pattern_2_tokens
                                .write_fmt(format_args!("__{field_name},", field_name = field_name))
                                .unwrap();

                            field_attributes.push(field_attribute);
                            field_names.push(field_name);
                        }

                        for (index, field_attribute) in field_attributes.into_iter().enumerate() {
                            let field_name = &field_names[index];

                            let compare_trait = field_attribute.compare_trait;
                            let compare_method = field_attribute.compare_method;

                            match compare_trait {
                                Some(compare_trait) => {
                                    let compare_method = compare_method.unwrap();

                                    block_tokens.write_fmt(format_args!("if !{compare_trait}::{compare_method}(_{field_name}, __{field_name}) {{ return false; }}", compare_trait = compare_trait, compare_method = compare_method, field_name = field_name)).unwrap();
                                }
                                None => {
                                    match compare_method {
                                        Some(compare_method) => {
                                            block_tokens.write_fmt(format_args!("if !{compare_method}(_{field_name}, __{field_name}) {{ return false; }}", compare_method = compare_method, field_name = field_name)).unwrap();
                                        }
                                        None => {
                                            block_tokens.write_fmt(format_args!("if core::cmp::PartialEq::ne(_{field_name}, __{field_name}) {{ return false; }}", field_name = field_name)).unwrap();
                                        }
                                    }
                                }
                            }
                        }

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}( {pattern_tokens} ) => {{ if let {enum_name}::{variant_ident} ( {pattern_2_tokens} ) = other {{ {block_tokens} }} else {{ return false; }} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, pattern_2_tokens = pattern_2_tokens, block_tokens = block_tokens)).unwrap();
                    }
                }
            }
        }

        match_tokens.push('}');

        comparer_tokens.extend(TokenStream::from_str(&match_tokens).unwrap());

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
                #[allow(clippy::unneeded_field_pattern)]
                fn eq(&self, other: &Self) -> bool {
                    #comparer_tokens

                    true
                }
            }
        };

        tokens.extend(compare_impl);
    }
}
