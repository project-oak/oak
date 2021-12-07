use std::fmt::Write;
use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::proc_macro2::TokenStream;
use crate::quote::ToTokens;
use crate::syn::{Data, DeriveInput, Fields, Generics, Lit, Meta};
use crate::Trait;

pub struct DefaultStructHandler;

impl TraitHandler for DefaultStructHandler {
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

        if let Data::Struct(data) = &ast.data {
            match type_attribute.expression {
                Some(expression) => {
                    for field in data.fields.iter() {
                        let _ = FieldAttributeBuilder {
                            enable_flag: false,
                            enable_literal: false,
                            enable_expression: false,
                        }
                        .from_attributes(&field.attrs, traits);
                    }

                    builder_tokens.extend(quote!(#expression));
                }
                None => {
                    match &data.fields {
                        Fields::Unit => {
                            let ident = &ast.ident;

                            builder_tokens.extend(quote!(#ident));
                        }
                        Fields::Unnamed(_) => {
                            let mut struct_tokens = ast.ident.to_string();

                            struct_tokens.push('(');

                            for field in data.fields.iter() {
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
                                                struct_tokens
                                                    .write_fmt(format_args!(
                                                        "core::convert::Into::into({s})",
                                                        s = s.into_token_stream().to_string()
                                                    ))
                                                    .unwrap();
                                            }
                                            _ => {
                                                struct_tokens.push_str(
                                                    &value.into_token_stream().to_string(),
                                                );
                                            }
                                        }
                                    }
                                    None => {
                                        match field_attribute.expression {
                                            Some(expression) => {
                                                struct_tokens.push_str(&expression);
                                            }
                                            None => {
                                                let typ = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                struct_tokens.write_fmt(format_args!("<{typ} as core::default::Default>::default()", typ = typ)).unwrap();
                                            }
                                        }
                                    }
                                }

                                struct_tokens.push(',');
                            }

                            struct_tokens.push(')');

                            builder_tokens.extend(TokenStream::from_str(&struct_tokens).unwrap());
                        }
                        Fields::Named(_) => {
                            let mut struct_tokens = ast.ident.to_string();

                            struct_tokens.push('{');

                            for field in data.fields.iter() {
                                let field_attribute = FieldAttributeBuilder {
                                    enable_flag: false,
                                    enable_literal: true,
                                    enable_expression: true,
                                }
                                .from_attributes(&field.attrs, traits);

                                let field_name = field.ident.as_ref().unwrap().to_string();

                                struct_tokens
                                    .write_fmt(format_args!(
                                        "{field_name}: ",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                match field_attribute.literal {
                                    Some(value) => {
                                        match &value {
                                            Lit::Str(s) => {
                                                struct_tokens
                                                    .write_fmt(format_args!(
                                                        "core::convert::Into::into({s})",
                                                        s = s.into_token_stream().to_string()
                                                    ))
                                                    .unwrap();
                                            }
                                            _ => {
                                                struct_tokens.push_str(
                                                    &value.into_token_stream().to_string(),
                                                );
                                            }
                                        }
                                    }
                                    None => {
                                        match field_attribute.expression {
                                            Some(expression) => {
                                                struct_tokens.push_str(&expression);
                                            }
                                            None => {
                                                let typ = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                struct_tokens.write_fmt(format_args!("<{typ} as core::default::Default>::default()", typ = typ)).unwrap();
                                            }
                                        }
                                    }
                                }

                                struct_tokens.push(',');
                            }

                            struct_tokens.push('}');

                            builder_tokens.extend(TokenStream::from_str(&struct_tokens).unwrap());
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
