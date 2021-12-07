use std::collections::BTreeMap;
use std::fmt::Write;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Fields, Generics, Meta};
use crate::Trait;

pub struct OrdEnumHandler;

impl TraitHandler for OrdEnumHandler {
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
        .from_ord_meta(meta);

        let enum_name = ast.ident.to_string();

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut comparer_tokens = TokenStream::new();

        let mut match_tokens = String::from("match self {");

        let mut has_non_unit_or_custom_value = false;

        if let Data::Enum(data) = &ast.data {
            let mut variant_values = Vec::new();
            let mut variant_idents = Vec::new();
            let mut variants = Vec::new();

            let mut variant_to_integer =
                String::from("let variant_to_integer = |other: &Self| match other {");
            let mut unit_to_integer =
                String::from("let unit_to_integer = |other: &Self| match other {");

            for (index, variant) in data.variants.iter().enumerate() {
                let variant_attribute = TypeAttributeBuilder {
                    enable_flag: false,
                    enable_bound: false,
                    rank: isize::min_value() + index as isize,
                    enable_rank: true,
                }
                .from_attributes(&variant.attrs, traits);

                let value = variant_attribute.rank;

                if variant_values.contains(&value) {
                    panic::reuse_a_value(value);
                }

                if value >= 0 {
                    has_non_unit_or_custom_value = true;
                }

                let variant_ident = variant.ident.to_string();

                match &variant.fields {
                    Fields::Unit => {
                        // TODO Unit
                        unit_to_integer.write_fmt(format_args!("{enum_name}::{variant_ident} => {enum_name}::{variant_ident} as isize,", enum_name = enum_name, variant_ident = variant_ident)).unwrap();
                        variant_to_integer
                            .write_fmt(format_args!(
                                "{enum_name}::{variant_ident} => {value},",
                                enum_name = enum_name,
                                variant_ident = variant_ident,
                                value = value
                            ))
                            .unwrap();
                    }
                    Fields::Named(_) => {
                        // TODO Struct
                        has_non_unit_or_custom_value = true;

                        variant_to_integer
                            .write_fmt(format_args!(
                                "{enum_name}::{variant_ident} {{ .. }} => {value},",
                                enum_name = enum_name,
                                variant_ident = variant_ident,
                                value = value
                            ))
                            .unwrap();
                    }
                    Fields::Unnamed(fields) => {
                        // TODO Tuple
                        has_non_unit_or_custom_value = true;

                        let mut pattern_tokens = String::new();

                        for _ in fields.unnamed.iter() {
                            pattern_tokens.push_str("_,");
                        }

                        variant_to_integer
                            .write_fmt(format_args!(
                                "{enum_name}::{variant_ident}( {pattern_tokens} ) => {value},",
                                enum_name = enum_name,
                                variant_ident = variant_ident,
                                pattern_tokens = pattern_tokens,
                                value = value
                            ))
                            .unwrap();
                    }
                }

                variant_values.push(value);
                variant_idents.push(variant_ident);
                variants.push(variant);
            }

            if has_non_unit_or_custom_value {
                variant_to_integer.push_str("};");

                comparer_tokens.extend(TokenStream::from_str(&variant_to_integer).unwrap());

                for (index, variant) in variants.into_iter().enumerate() {
                    let variant_value = variant_values[index];
                    let variant_ident = &variant_idents[index];

                    match &variant.fields {
                        Fields::Unit => {
                            // TODO Unit
                            match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ let other_value = variant_to_integer(other); return core::cmp::Ord::cmp(&{variant_value}, &other_value); }}", enum_name = enum_name, variant_ident = variant_ident, variant_value = variant_value)).unwrap();
                        }
                        Fields::Named(fields) => {
                            // TODO Struct
                            let mut pattern_tokens = String::new();
                            let mut pattern_2_tokens = String::new();
                            let mut block_tokens = String::new();

                            let mut field_attributes = BTreeMap::new();
                            let mut field_names = BTreeMap::new();

                            for (index, field) in fields.named.iter().enumerate() {
                                let field_attribute = FieldAttributeBuilder {
                                    enable_ignore: true,
                                    enable_impl: true,
                                    rank: isize::min_value() + index as isize,
                                    enable_rank: true,
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

                                let rank = field_attribute.rank;

                                if field_attributes.contains_key(&rank) {
                                    panic::reuse_a_rank(rank);
                                }

                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_2_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}: ___{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();

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

                                        block_tokens.write_fmt(format_args!("match {compare_trait}::{compare_method}({field_name}, ___{field_name}) {{ core::cmp::Ordering::Equal => (), core::cmp::Ordering::Greater => {{ return core::cmp::Ordering::Greater; }}, core::cmp::Ordering::Less => {{ return core::cmp::Ordering::Less; }} }}", compare_trait = compare_trait, compare_method = compare_method, field_name = field_name)).unwrap();
                                    }
                                    None => {
                                        match compare_method {
                                            Some(compare_method) => {
                                                block_tokens.write_fmt(format_args!("match {compare_method}({field_name}, ___{field_name}) {{ core::cmp::Ordering::Equal => (), core::cmp::Ordering::Greater => {{ return core::cmp::Ordering::Greater; }}, core::cmp::Ordering::Less => {{ return core::cmp::Ordering::Less; }} }}", compare_method = compare_method, field_name = field_name)).unwrap();
                                            }
                                            None => {
                                                block_tokens.write_fmt(format_args!("match core::cmp::Ord::cmp({field_name}, ___{field_name}) {{ core::cmp::Ordering::Equal => (), core::cmp::Ordering::Greater => {{ return core::cmp::Ordering::Greater; }}, core::cmp::Ordering::Less => {{ return core::cmp::Ordering::Less; }} }}", field_name = field_name)).unwrap();
                                            }
                                        }
                                    }
                                }
                            }

                            match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}{{ {pattern_tokens} }} => {{ if let {enum_name}::{variant_ident} {{ {pattern_2_tokens} }} = other {{ {block_tokens} }} else {{ let other_value = variant_to_integer(other); return core::cmp::Ord::cmp(&{variant_value}, &other_value); }} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, pattern_2_tokens = pattern_2_tokens, block_tokens = block_tokens, variant_value = variant_value)).unwrap();
                        }
                        Fields::Unnamed(fields) => {
                            // TODO Tuple
                            let mut pattern_tokens = String::new();
                            let mut pattern_2_tokens = String::new();
                            let mut block_tokens = String::new();

                            let mut field_attributes = BTreeMap::new();
                            let mut field_names = BTreeMap::new();

                            for (index, field) in fields.unnamed.iter().enumerate() {
                                let field_attribute = FieldAttributeBuilder {
                                    enable_ignore: true,
                                    enable_impl: true,
                                    rank: isize::min_value() + index as isize,
                                    enable_rank: true,
                                }
                                .from_attributes(&field.attrs, traits);

                                let field_name = format!("{}", index);

                                if field_attribute.ignore {
                                    pattern_tokens.push_str("_,");
                                    pattern_2_tokens.push_str("_,");
                                    continue;
                                }

                                let rank = field_attribute.rank;

                                if field_attributes.contains_key(&rank) {
                                    panic::reuse_a_rank(rank);
                                }

                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "_{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_2_tokens
                                    .write_fmt(format_args!(
                                        "__{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();

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

                                        block_tokens.write_fmt(format_args!("match {compare_trait}::{compare_method}(_{field_name}, __{field_name}) {{ core::cmp::Ordering::Equal => (), core::cmp::Ordering::Greater => {{ return core::cmp::Ordering::Greater; }}, core::cmp::Ordering::Less => {{ return core::cmp::Ordering::Less; }} }}", compare_trait = compare_trait, compare_method = compare_method, field_name = field_name)).unwrap();
                                    }
                                    None => {
                                        match compare_method {
                                            Some(compare_method) => {
                                                block_tokens.write_fmt(format_args!("match {compare_method}(_{field_name}, __{field_name}) {{ core::cmp::Ordering::Equal => (), core::cmp::Ordering::Greater => {{ return core::cmp::Ordering::Greater; }}, core::cmp::Ordering::Less => {{ return core::cmp::Ordering::Less; }} }}", compare_method = compare_method, field_name = field_name)).unwrap();
                                            }
                                            None => {
                                                block_tokens.write_fmt(format_args!("match core::cmp::Ord::cmp(_{field_name}, __{field_name}) {{ core::cmp::Ordering::Equal => (), core::cmp::Ordering::Greater => {{ return core::cmp::Ordering::Greater; }}, core::cmp::Ordering::Less => {{ return core::cmp::Ordering::Less; }} }}", field_name = field_name)).unwrap();
                                            }
                                        }
                                    }
                                }
                            }

                            match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}( {pattern_tokens} ) => {{ if let {enum_name}::{variant_ident} ( {pattern_2_tokens} ) = other {{ {block_tokens} }} else {{ let other_value = variant_to_integer(other); return core::cmp::Ord::cmp(&{variant_value}, &other_value); }} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, pattern_2_tokens = pattern_2_tokens, block_tokens = block_tokens, variant_value = variant_value)).unwrap();
                        }
                    }
                }
            } else {
                unit_to_integer.push_str("};");

                comparer_tokens.extend(TokenStream::from_str(&unit_to_integer).unwrap());

                for (index, _) in variants.into_iter().enumerate() {
                    let variant_ident = &variant_idents[index];

                    match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ let other_value = unit_to_integer(other); return core::cmp::Ord::cmp(&({enum_name}::{variant_ident} as isize), &other_value); }}", enum_name = enum_name, variant_ident = variant_ident)).unwrap();
                }
            }
        }

        match_tokens.push('}');

        comparer_tokens.extend(TokenStream::from_str(&match_tokens).unwrap());

        if has_non_unit_or_custom_value {
            comparer_tokens.extend(quote!(core::cmp::Ordering::Equal));
        }

        let ident = &ast.ident;

        let mut generics_cloned: Generics = ast.generics.clone();

        let where_clause = generics_cloned.make_where_clause();

        for where_predicate in bound {
            where_clause.predicates.push(where_predicate);
        }

        let (impl_generics, ty_generics, where_clause) = generics_cloned.split_for_impl();

        let compare_impl = quote! {
            impl #impl_generics core::cmp::Ord for #ident #ty_generics #where_clause {
                #[inline]
                #[allow(unreachable_code, clippy::unneeded_field_pattern)]
                fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                    #comparer_tokens
                }
            }
        };

        tokens.extend(compare_impl);
    }
}
