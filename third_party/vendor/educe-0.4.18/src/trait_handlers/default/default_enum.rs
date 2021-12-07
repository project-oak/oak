use std::fmt::Write;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::quote::ToTokens;
use crate::syn::{Data, DeriveInput, Fields, Generics, Lit, Meta};
use crate::Trait;

pub struct DefaultEnumHandler;

impl TraitHandler for DefaultEnumHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_flag: true,
            enable_new: true,
            enable_expression: true,
            enable_bound: true,
        }
        .from_default_meta(meta);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut builder_tokens = TokenStream::new();

        if let Data::Enum(data) = &ast.data {
            match type_attribute.expression {
                Some(expression) => {
                    for variant in data.variants.iter() {
                        let _ = TypeAttributeBuilder {
                            enable_flag: false,
                            enable_new: false,
                            enable_expression: false,
                            enable_bound: false,
                        }
                        .from_attributes(&variant.attrs, traits);

                        ensure_fields_no_attribute(&variant.fields, traits);
                    }

                    builder_tokens.extend(quote!(#expression));
                }
                None => {
                    let variant = {
                        let variants = &data.variants;

                        if variants.len() == 1 {
                            let variant = &variants[0];

                            let _ = TypeAttributeBuilder {
                                enable_flag: true,
                                enable_new: false,
                                enable_expression: false,
                                enable_bound: false,
                            }
                            .from_attributes(&variant.attrs, traits);

                            variant
                        } else {
                            let mut variants_iter = variants.iter();

                            loop {
                                let variant = variants_iter.next();

                                match variant {
                                    Some(variant) => {
                                        let variant_attribute = TypeAttributeBuilder {
                                            enable_flag: true,
                                            enable_new: false,
                                            enable_expression: false,
                                            enable_bound: false,
                                        }
                                        .from_attributes(&variant.attrs, traits);

                                        if variant_attribute.flag {
                                            loop {
                                                let variant = variants_iter.next();

                                                match variant {
                                                    Some(variant) => {
                                                        let variant_attribute = TypeAttributeBuilder {
                                                            enable_flag: true,
                                                            enable_new: false,
                                                            enable_expression: false,
                                                            enable_bound: false,
                                                        }.from_attributes(&variant.attrs, traits);

                                                        if variant_attribute.flag {
                                                            panic::multiple_default_variants();
                                                        } else {
                                                            ensure_fields_no_attribute(
                                                                &variant.fields,
                                                                traits,
                                                            );
                                                        }
                                                    }
                                                    None => break,
                                                }
                                            }

                                            break variant;
                                        } else {
                                            ensure_fields_no_attribute(&variant.fields, traits);
                                        }
                                    }
                                    None => panic::no_default_variant(),
                                }
                            }
                        }
                    };

                    let enum_name = ast.ident.to_string();
                    let variant_name = variant.ident.to_string();

                    let mut enum_tokens = format!(
                        "{enum_name}::{variant_name}",
                        enum_name = enum_name,
                        variant_name = variant_name
                    );

                    match &variant.fields {
                        Fields::Unit => (), // TODO Unit
                        Fields::Named(fields) => {
                            // TODO Struct
                            enum_tokens.push('{');

                            for field in fields.named.iter() {
                                let field_attribute = FieldAttributeBuilder {
                                    enable_flag: false,
                                    enable_literal: true,
                                    enable_expression: true,
                                }
                                .from_attributes(&field.attrs, traits);

                                let field_name = field.ident.as_ref().unwrap().to_string();

                                enum_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}: ",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                match field_attribute.literal {
                                    Some(value) => {
                                        match &value {
                                            Lit::Str(s) => {
                                                enum_tokens
                                                    .write_fmt(format_args!(
                                                        "core::convert::Into::into({s})",
                                                        s = s.into_token_stream().to_string()
                                                    ))
                                                    .unwrap();
                                            }
                                            _ => {
                                                enum_tokens.push_str(
                                                    &value.into_token_stream().to_string(),
                                                );
                                            }
                                        }
                                    }
                                    None => {
                                        match field_attribute.expression {
                                            Some(expression) => {
                                                enum_tokens.push_str(&expression);
                                            }
                                            None => {
                                                let typ = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                enum_tokens.write_fmt(format_args!("<{typ} as core::default::Default>::default()", typ = typ)).unwrap();
                                            }
                                        }
                                    }
                                }

                                enum_tokens.push(',');
                            }

                            enum_tokens.push('}');
                        }
                        Fields::Unnamed(fields) => {
                            // TODO Tuple
                            enum_tokens.push('(');

                            for field in fields.unnamed.iter() {
                                let field_attribute = FieldAttributeBuilder {
                                    enable_flag: false,
                                    enable_literal: true,
                                    enable_expression: true,
                                }
                                .from_attributes(&field.attrs, traits);

                                match field_attribute.literal {
                                    Some(value) => {
                                        match &value {
                                            Lit::Str(s) => {
                                                enum_tokens
                                                    .write_fmt(format_args!(
                                                        "core::convert::Into::into({s})",
                                                        s = s.into_token_stream().to_string()
                                                    ))
                                                    .unwrap();
                                            }
                                            _ => {
                                                enum_tokens.push_str(
                                                    &value.into_token_stream().to_string(),
                                                );
                                            }
                                        }
                                    }
                                    None => {
                                        match field_attribute.expression {
                                            Some(expression) => {
                                                enum_tokens.push_str(&expression);
                                            }
                                            None => {
                                                let typ = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                enum_tokens.write_fmt(format_args!("<{typ} as core::default::Default>::default()", typ = typ)).unwrap();
                                            }
                                        }
                                    }
                                }

                                enum_tokens.push(',');
                            }

                            enum_tokens.push(')');
                        }
                    }

                    builder_tokens.extend(TokenStream::from_str(&enum_tokens).unwrap());
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

        let default_impl = quote! {
            impl #impl_generics core::default::Default for #ident #ty_generics #where_clause {
                #[inline]
                fn default() -> Self {
                    #builder_tokens
                }
            }
        };

        tokens.extend(default_impl);

        if type_attribute.new {
            let new_impl = quote! {
                impl #impl_generics #ident #ty_generics #where_clause {
                    /// Returns the "default value" for a type.
                    #[inline]
                    pub fn new() -> Self {
                        <Self as core::default::Default>::default()
                    }
                }
            };

            tokens.extend(new_impl);
        }
    }
}

fn ensure_fields_no_attribute(fields: &Fields, traits: &[Trait]) {
    match fields {
        Fields::Unit => (),
        Fields::Named(fields) => {
            for field in fields.named.iter() {
                let _ = FieldAttributeBuilder {
                    enable_flag: false,
                    enable_literal: false,
                    enable_expression: false,
                }
                .from_attributes(&field.attrs, traits);
            }
        }
        Fields::Unnamed(fields) => {
            for field in fields.unnamed.iter() {
                let _ = FieldAttributeBuilder {
                    enable_flag: false,
                    enable_literal: false,
                    enable_expression: false,
                }
                .from_attributes(&field.attrs, traits);
            }
        }
    }
}
