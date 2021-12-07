use std::fmt::Write;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttribute, FieldAttributeBuilder, TypeAttributeBuilder};

use crate::proc_macro2::TokenStream;
use crate::syn::{punctuated::Punctuated, Data, DeriveInput, Fields, Generics, Meta};
use crate::Trait;

pub struct CloneEnumHandler;

impl TraitHandler for CloneEnumHandler {
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
        .from_clone_meta(meta);

        let mut bound = Punctuated::new();

        let mut clone_tokens = TokenStream::new();
        let mut clone_from_tokens = TokenStream::new();

        if let Data::Enum(data) = &ast.data {
            let mut variant_idents = Vec::new();
            let mut field_attributes_names: Vec<(bool, Vec<FieldAttribute>, Vec<String>)> =
                Vec::new();

            #[cfg(feature = "Copy")]
            let mut has_custom_clone_method = false;

            for variant in data.variants.iter() {
                let _ = TypeAttributeBuilder {
                    enable_flag: false,
                    enable_bound: false,
                }
                .from_attributes(&variant.attrs, traits);

                let mut field_attributes = Vec::new();
                let mut field_names = Vec::new();
                let mut is_tuple = true;

                match &variant.fields {
                    Fields::Unit => (),
                    Fields::Named(fields) => {
                        // TODO Struct
                        is_tuple = false;

                        for field in fields.named.iter() {
                            let field_attribute = FieldAttributeBuilder {
                                enable_impl: true,
                            }
                            .from_attributes(&field.attrs, traits);

                            let field_name = field.ident.as_ref().unwrap().to_string();

                            #[cfg(feature = "Copy")]
                            if field_attribute.clone_method.is_some() {
                                has_custom_clone_method = true;
                            }

                            field_attributes.push(field_attribute);
                            field_names.push(field_name);
                        }
                    }
                    Fields::Unnamed(fields) => {
                        // TODO Tuple
                        for (index, field) in fields.unnamed.iter().enumerate() {
                            let field_attribute = FieldAttributeBuilder {
                                enable_impl: true,
                            }
                            .from_attributes(&field.attrs, traits);

                            let field_name = format!("_{}", index);

                            #[cfg(feature = "Copy")]
                            if field_attribute.clone_method.is_some() {
                                has_custom_clone_method = true;
                            }

                            field_attributes.push(field_attribute);
                            field_names.push(field_name);
                        }
                    }
                }

                variant_idents.push(variant.ident.to_string());
                field_attributes_names.push((is_tuple, field_attributes, field_names));
            }

            let enum_name = ast.ident.to_string();

            #[cfg(feature = "Copy")]
            let contains_copy = !has_custom_clone_method && traits.contains(&Trait::Copy);

            #[cfg(not(feature = "Copy"))]
            let contains_copy = false;

            if contains_copy {
                bound = type_attribute
                    .bound
                    .into_punctuated_where_predicates_by_generic_parameters_with_copy(
                        &ast.generics.params,
                    );

                clone_tokens.extend(quote!(*self));

                let mut match_tokens = String::from("match self {");

                for (index, variant_ident) in variant_idents.iter().enumerate() {
                    let field_attributes_names = &field_attributes_names[index];
                    let is_tuple = field_attributes_names.0;
                    let field_attributes = &field_attributes_names.1;
                    let field_names = &field_attributes_names.2;
                    let is_unit = field_names.is_empty();

                    if is_unit {
                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ if let {enum_name}::{variant_ident} = _source {{ done = true; }} }}", enum_name = enum_name, variant_ident = variant_ident)).unwrap();
                    } else {
                        let mut pattern_tokens = String::new();
                        let mut pattern_2_tokens = String::new();

                        if is_tuple {
                            for field_name in field_names {
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_2_tokens
                                    .write_fmt(format_args!(
                                        "___{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            }
                        } else {
                            for field_name in field_names {
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
                            }
                        }

                        let mut block_tokens = String::new();

                        for (index, field_attribute) in field_attributes.iter().enumerate() {
                            let field_name = &field_names[index];

                            let clone_trait = &field_attribute.clone_trait;
                            let clone_method = &field_attribute.clone_method;

                            match clone_trait {
                                Some(clone_trait) => {
                                    let clone_method = clone_method.as_ref().unwrap();

                                    block_tokens.write_fmt(format_args!("*{field_name} = {clone_trait}::{clone_method}(___{field_name});", clone_trait = clone_trait, clone_method = clone_method, field_name = field_name)).unwrap();
                                }
                                None => {
                                    match clone_method {
                                        Some(clone_method) => {
                                            block_tokens.write_fmt(format_args!("*{field_name} = {clone_method}(___{field_name});", clone_method = clone_method, field_name = field_name)).unwrap();
                                        }
                                        None => {
                                            block_tokens.write_fmt(format_args!("core::clone::Clone::clone_from({field_name}, ___{field_name});", field_name = field_name)).unwrap();
                                        }
                                    }
                                }
                            }
                        }

                        if is_tuple {
                            match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} ( {pattern_tokens} ) => {{ if let {enum_name}::{variant_ident} ( {pattern_2_tokens} ) = _source {{ {block_tokens} done = true; }} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, pattern_2_tokens = pattern_2_tokens, block_tokens = block_tokens)).unwrap();
                        } else {
                            match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} {{ {pattern_tokens} }} => {{ if let {enum_name}::{variant_ident} {{ {pattern_2_tokens} }} = _source {{ {block_tokens} }} done = true; }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, pattern_2_tokens = pattern_2_tokens, block_tokens = block_tokens)).unwrap();
                        }
                    }
                }

                match_tokens.push('}');

                clone_from_tokens.extend(TokenStream::from_str(&match_tokens).unwrap());
            } else {
                bound = type_attribute
                    .bound
                    .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

                let mut clone_match_tokens = String::from("match self {");
                let mut clone_from_match_tokens = String::from("match self {");

                for (index, variant_ident) in variant_idents.iter().enumerate() {
                    let field_attributes_names = &field_attributes_names[index];
                    let is_tuple = field_attributes_names.0;
                    let field_attributes = &field_attributes_names.1;
                    let field_names = &field_attributes_names.2;
                    let is_unit = field_names.is_empty();

                    if is_unit {
                        clone_match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ {enum_name}::{variant_ident} }}", enum_name = enum_name, variant_ident = variant_ident)).unwrap();
                        clone_from_match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ if let {enum_name}::{variant_ident} = _source {{ done = true; }} }}", enum_name = enum_name, variant_ident = variant_ident)).unwrap();
                    } else {
                        let mut pattern_tokens = String::new();
                        let mut pattern_2_tokens = String::new();
                        let mut pattern_3_tokens = String::new();

                        if is_tuple {
                            let mut clone = format!(
                                "{enum_name}::{variant_ident}(",
                                enum_name = enum_name,
                                variant_ident = variant_ident
                            );
                            let mut clone_from = String::new();

                            for field_name in field_names {
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_2_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_3_tokens
                                    .write_fmt(format_args!(
                                        "___{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            }

                            for (index, field_attribute) in field_attributes.iter().enumerate() {
                                let field_name = &field_names[index];

                                let clone_trait = &field_attribute.clone_trait;
                                let clone_method = &field_attribute.clone_method;

                                match clone_trait {
                                    Some(clone_trait) => {
                                        let clone_method = clone_method.as_ref().unwrap();

                                        clone
                                            .write_fmt(format_args!(
                                                "{clone_trait}::{clone_method}({field_name}),",
                                                clone_trait = clone_trait,
                                                clone_method = clone_method,
                                                field_name = field_name
                                            ))
                                            .unwrap();
                                        clone_from.write_fmt(format_args!("*{field_name} = {clone_trait}::{clone_method}(___{field_name});", clone_trait = clone_trait, clone_method = clone_method, field_name = field_name)).unwrap();
                                    }
                                    None => {
                                        match clone_method {
                                            Some(clone_method) => {
                                                clone
                                                    .write_fmt(format_args!(
                                                        "{clone_method}({field_name}),",
                                                        clone_method = clone_method,
                                                        field_name = field_name
                                                    ))
                                                    .unwrap();
                                                clone_from.write_fmt(format_args!("*{field_name} = {clone_method}(___{field_name});", clone_method = clone_method, field_name = field_name)).unwrap();
                                            }
                                            None => {
                                                clone
                                                    .write_fmt(format_args!(
                                                        "core::clone::Clone::clone({field_name}),",
                                                        field_name = field_name
                                                    ))
                                                    .unwrap();
                                                clone_from.write_fmt(format_args!("core::clone::Clone::clone_from({field_name}, ___{field_name});", field_name = field_name)).unwrap();
                                            }
                                        }
                                    }
                                }
                            }

                            clone.push(')');

                            clone_match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} ( {pattern_tokens} ) => {{ {clone} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, clone = clone)).unwrap();
                            clone_from_match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} ( {pattern_2_tokens} ) => {{ if let {enum_name}::{variant_ident} ( {pattern_3_tokens} ) = _source {{ {block_tokens} done = true; }} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_2_tokens = pattern_2_tokens, pattern_3_tokens = pattern_3_tokens, block_tokens = clone_from)).unwrap();
                        } else {
                            let mut clone = format!(
                                "{enum_name}::{variant_ident} {{",
                                enum_name = enum_name,
                                variant_ident = variant_ident
                            );
                            let mut clone_from = String::new();

                            for field_name in field_names {
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_2_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_3_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}: ___{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            }

                            for (index, field_attribute) in field_attributes.iter().enumerate() {
                                let field_name = &field_names[index];

                                let clone_trait = &field_attribute.clone_trait;
                                let clone_method = &field_attribute.clone_method;

                                match clone_trait {
                                    Some(clone_trait) => {
                                        let clone_method = clone_method.as_ref().unwrap();

                                        clone.write_fmt(format_args!("{field_name}: {clone_trait}::{clone_method}({field_name}),", clone_trait = clone_trait, clone_method = clone_method, field_name = field_name)).unwrap();
                                        clone_from.write_fmt(format_args!("*{field_name} = {clone_trait}::{clone_method}(___{field_name});", clone_trait = clone_trait, clone_method = clone_method, field_name = field_name)).unwrap();
                                    }
                                    None => {
                                        match clone_method {
                                            Some(clone_method) => {
                                                clone.write_fmt(format_args!("{field_name}: {clone_method}({field_name}),", clone_method = clone_method, field_name = field_name)).unwrap();
                                                clone_from.write_fmt(format_args!("*{field_name} = {clone_method}(___{field_name});", clone_method = clone_method, field_name = field_name)).unwrap();
                                            }
                                            None => {
                                                clone.write_fmt(format_args!("{field_name}: core::clone::Clone::clone({field_name}),", field_name = field_name)).unwrap();
                                                clone_from.write_fmt(format_args!("core::clone::Clone::clone_from({field_name}, ___{field_name});", field_name = field_name)).unwrap();
                                            }
                                        }
                                    }
                                }
                            }

                            clone.push('}');

                            clone_match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} {{ {pattern_tokens} }} => {{ {clone} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, clone = clone)).unwrap();
                            clone_from_match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} {{ {pattern_2_tokens} }} => {{ if let {enum_name}::{variant_ident} {{ {pattern_3_tokens} }} = _source {{ {block_tokens} }} done = true; }}", enum_name = enum_name, variant_ident = variant_ident, pattern_2_tokens = pattern_2_tokens, pattern_3_tokens = pattern_3_tokens, block_tokens = clone_from)).unwrap();
                        }
                    }
                }

                clone_match_tokens.push('}');
                clone_from_match_tokens.push('}');

                clone_tokens.extend(TokenStream::from_str(&clone_match_tokens).unwrap());
                clone_from_tokens.extend(TokenStream::from_str(&clone_from_match_tokens).unwrap());
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
            impl #impl_generics core::clone::Clone for #ident #ty_generics #where_clause {
                #[inline]
                fn clone(&self) -> Self {
                    #clone_tokens
                }

                #[inline]
                fn clone_from(&mut self, _source: &Self) {
                    let mut done = false;

                    #clone_from_tokens

                    if !done {
                        *self = core::clone::Clone::clone(_source);
                    }
                }
            }
        };

        tokens.extend(compare_impl);
    }
}
