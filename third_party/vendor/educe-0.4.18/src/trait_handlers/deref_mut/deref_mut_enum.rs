use std::fmt::Write;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Fields, Meta};
use crate::Trait;

pub struct DerefMutEnumHandler;

impl TraitHandler for DerefMutEnumHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let _ = TypeAttributeBuilder {
            enable_flag: true,
        }
        .from_deref_mut_meta(meta);

        let enum_name = ast.ident.to_string();

        let mut deref_mut_tokens = TokenStream::new();

        let mut match_tokens = String::from("match self {");

        if let Data::Enum(data) = &ast.data {
            for variant in data.variants.iter() {
                let _ = TypeAttributeBuilder {
                    enable_flag: false,
                }
                .from_attributes(&variant.attrs, traits);

                let variant_ident = variant.ident.to_string();

                match &variant.fields {
                    Fields::Unit => {
                        // TODO Unit
                        panic::deref_mut_cannot_support_unit_variant();
                    }
                    Fields::Named(fields) => {
                        // TODO Struct
                        let mut pattern_tokens = String::new();
                        let mut block_tokens = String::new();

                        let mut counter = 0;

                        for field in fields.named.iter() {
                            let field_attribute = FieldAttributeBuilder {
                                enable_flag: true,
                            }
                            .from_attributes(&field.attrs, traits);

                            if field_attribute.flag {
                                if !block_tokens.is_empty() {
                                    panic::multiple_deref_mut_fields_of_variant(&variant_ident);
                                }

                                let field_name = field.ident.as_ref().unwrap().to_string();

                                block_tokens
                                    .write_fmt(format_args!(
                                        "return {field_name};",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}, ..",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            }

                            counter += 1;
                        }

                        if block_tokens.is_empty() {
                            if counter == 1 {
                                let field = fields.named.iter().next().unwrap();

                                let field_name = field.ident.as_ref().unwrap().to_string();

                                block_tokens
                                    .write_fmt(format_args!(
                                        "return {field_name};",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}, ..",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            } else {
                                panic::no_deref_mut_field_of_variant(&variant_ident);
                            }
                        }

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} {{ {pattern_tokens} }} => {{ {block_tokens} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, block_tokens = block_tokens)).unwrap();
                    }
                    Fields::Unnamed(fields) => {
                        // TODO Tuple
                        let mut pattern_tokens = String::new();
                        let mut block_tokens = String::new();

                        let mut counter = 0;

                        for (index, field) in fields.unnamed.iter().enumerate() {
                            let field_attribute = FieldAttributeBuilder {
                                enable_flag: true,
                            }
                            .from_attributes(&field.attrs, traits);

                            if field_attribute.flag {
                                if !block_tokens.is_empty() {
                                    panic::multiple_deref_mut_fields_of_variant(&variant_ident);
                                }

                                let field_name = format!("{}", index);

                                block_tokens
                                    .write_fmt(format_args!(
                                        "return _{field_name};",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "_{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            } else {
                                pattern_tokens.push_str("_,");
                            }

                            counter += 1;
                        }

                        if block_tokens.is_empty() {
                            if counter == 1 {
                                let field_name = String::from("0");

                                block_tokens
                                    .write_fmt(format_args!(
                                        "return _{field_name};",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                pattern_tokens.clear();
                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "_{field_name}",
                                        field_name = field_name
                                    ))
                                    .unwrap();
                            } else {
                                panic::no_deref_mut_field_of_variant(&variant_ident);
                            }
                        }

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}( {pattern_tokens} ) => {{ {block_tokens} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, block_tokens = block_tokens)).unwrap();
                    }
                }
            }
        }

        match_tokens.push('}');

        deref_mut_tokens.extend(TokenStream::from_str(&match_tokens).unwrap());

        let ident = &ast.ident;

        let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

        let deref_mut_impl = quote! {
            impl #impl_generics core::ops::DerefMut for #ident #ty_generics #where_clause {
                #[inline]
                fn deref_mut(&mut self) -> &mut Self::Target {
                    #deref_mut_tokens
                }
            }
        };

        tokens.extend(deref_mut_impl);
    }
}
