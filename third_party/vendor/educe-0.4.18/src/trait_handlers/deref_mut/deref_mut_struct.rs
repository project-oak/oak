use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{FieldAttributeBuilder, TypeAttributeBuilder};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

pub struct DerefMutStructHandler;

impl TraitHandler for DerefMutStructHandler {
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

        let mut deref_mut_tokens = TokenStream::new();

        if let Data::Struct(data) = &ast.data {
            let mut counter = 0;

            for (index, field) in data.fields.iter().enumerate() {
                let field_attribute = FieldAttributeBuilder {
                    enable_flag: true,
                }
                .from_attributes(&field.attrs, traits);

                if field_attribute.flag {
                    if !deref_mut_tokens.is_empty() {
                        panic::multiple_deref_mut_fields();
                    }

                    let field_name = if let Some(ident) = field.ident.as_ref() {
                        ident.to_string()
                    } else {
                        format!("{}", index)
                    };

                    deref_mut_tokens.extend(
                        TokenStream::from_str(&format!(
                            "&mut self.{field_name}",
                            field_name = field_name
                        ))
                        .unwrap(),
                    );
                }

                counter += 1;
            }

            if deref_mut_tokens.is_empty() {
                if counter == 1 {
                    let field = data.fields.iter().next().unwrap();

                    let field_name = if let Some(ident) = field.ident.as_ref() {
                        ident.to_string()
                    } else {
                        String::from("0")
                    };

                    deref_mut_tokens.extend(
                        TokenStream::from_str(&format!(
                            "&mut self.{field_name}",
                            field_name = field_name
                        ))
                        .unwrap(),
                    );
                } else {
                    panic::no_deref_mut_field();
                }
            }
        }

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
