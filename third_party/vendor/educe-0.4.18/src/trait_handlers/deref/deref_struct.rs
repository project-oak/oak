use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::quote::ToTokens;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

pub struct DerefStructHandler;

impl TraitHandler for DerefStructHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let _ = TypeAttributeBuilder {
            enable_flag: true,
        }
        .from_deref_meta(meta);

        let mut ty = TokenStream::new();
        let mut deref_tokens = TokenStream::new();

        if let Data::Struct(data) = &ast.data {
            let mut counter = 0;

            for (index, field) in data.fields.iter().enumerate() {
                let field_attribute = FieldAttributeBuilder {
                    enable_flag: true,
                }
                .from_attributes(&field.attrs, traits);

                if field_attribute.flag {
                    if !ty.is_empty() {
                        panic::multiple_deref_fields();
                    }

                    let field_name = if let Some(ident) = field.ident.as_ref() {
                        ident.to_string()
                    } else {
                        format!("{}", index)
                    };

                    ty.extend(field.ty.clone().into_token_stream());
                    deref_tokens.extend(
                        TokenStream::from_str(&format!(
                            "&self.{field_name}",
                            field_name = field_name
                        ))
                        .unwrap(),
                    );
                }

                counter += 1;
            }

            if ty.is_empty() {
                if counter == 1 {
                    let field = data.fields.iter().next().unwrap();

                    let field_name = if let Some(ident) = field.ident.as_ref() {
                        ident.to_string()
                    } else {
                        String::from("0")
                    };

                    ty.extend(field.ty.clone().into_token_stream());
                    deref_tokens.extend(
                        TokenStream::from_str(&format!(
                            "&self.{field_name}",
                            field_name = field_name
                        ))
                        .unwrap(),
                    );
                } else {
                    panic::no_deref_field();
                }
            }
        }

        let ident = &ast.ident;

        let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

        let deref_impl = quote! {
            impl #impl_generics core::ops::Deref for #ident #ty_generics #where_clause {
                type Target = #ty;

                #[inline]
                fn deref(&self) -> &Self::Target {
                    #deref_tokens
                }
            }
        };

        tokens.extend(deref_impl);
    }
}
