use std::str::FromStr;

use super::super::TraitHandler;
use super::models::{
    FieldAttributeBuilder, FieldAttributeName, TypeAttributeBuilder, TypeAttributeName,
};

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::quote::ToTokens;
use crate::syn::{Data, DeriveInput, Fields, Generics, Meta};
use crate::Trait;

pub struct DebugStructHandler;

impl TraitHandler for DebugStructHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let is_tuple = {
            if let Data::Struct(data) = &ast.data {
                matches!(data.fields, Fields::Unnamed(_))
            } else {
                true
            }
        };

        let type_attribute = TypeAttributeBuilder {
            enable_flag: true,
            name: TypeAttributeName::Default,
            enable_name: true,
            named_field: !is_tuple,
            enable_named_field: true,
            enable_bound: true,
        }
        .from_debug_meta(meta);

        let name = type_attribute.name.into_string_by_ident(&ast.ident);

        let named_field = type_attribute.named_field;

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut builder_tokens = TokenStream::new();
        let mut has_fields = false;

        if named_field {
            if name.is_empty() {
                builder_tokens.extend(quote!(
                    struct RawString(&'static str);

                    impl core::fmt::Debug for RawString {
                        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                            f.write_str(self.0)
                        }
                    }
                ));
                builder_tokens.extend(quote!(let mut builder = formatter.debug_map();));
            } else {
                builder_tokens.extend(quote!(let mut builder = formatter.debug_struct(#name);));
            }

            if let Data::Struct(data) = &ast.data {
                for (index, field) in data.fields.iter().enumerate() {
                    let field_attribute = FieldAttributeBuilder {
                        name: FieldAttributeName::Default,
                        enable_name: true,
                        enable_ignore: true,
                        enable_impl: true,
                    }
                    .from_attributes(&field.attrs, traits);

                    if field_attribute.ignore {
                        continue;
                    }

                    let rename = field_attribute.name.into_option_string();

                    let format_trait = field_attribute.format_trait;
                    let format_method = field_attribute.format_method;

                    let (key, field_name) = match rename {
                        Some(rename) => {
                            if let Some(ident) = field.ident.as_ref() {
                                (rename, ident.to_string())
                            } else {
                                (rename, format!("{}", index))
                            }
                        }
                        None => {
                            if let Some(ident) = field.ident.as_ref() {
                                (ident.to_string(), ident.to_string())
                            } else {
                                (format!("_{}", index), format!("{}", index))
                            }
                        }
                    };

                    match format_trait {
                        Some(format_trait) => {
                            let format_method = format_method.unwrap();

                            builder_tokens.extend(TokenStream::from_str(&format!("
                                let arg = {{
                                    struct MyDebug<'a, T: {format_trait}>(&'a T);

                                    impl<'a, T: {format_trait}> core::fmt::Debug for MyDebug<'a, T> {{
                                        fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                            {format_trait}::{format_method}(self.0, formatter)
                                        }}
                                    }}

                                    MyDebug(&self.{field_name})
                                }};
                            ", format_trait = format_trait, format_method = format_method, field_name = field_name)).unwrap());

                            let statement = if name.is_empty() {
                                format!("builder.entry(&RawString({key:?}), &arg);", key = key)
                            } else {
                                format!("builder.field({key:?}, &arg);", key = key)
                            };

                            builder_tokens.extend(TokenStream::from_str(&statement).unwrap());
                        }
                        None => {
                            match format_method {
                                Some(format_method) => {
                                    let ty = field.ty.clone().into_token_stream().to_string();

                                    builder_tokens.extend(TokenStream::from_str(&format!("
                                        let arg = {{
                                            struct MyDebug<'a>(&'a {ty});

                                            impl<'a> core::fmt::Debug for MyDebug<'a> {{
                                                fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                    {format_method}(self.0, formatter)
                                                }}
                                            }}

                                            MyDebug(&self.{field_name})
                                        }};
                                    ", ty = ty, format_method = format_method, field_name = field_name)).unwrap());

                                    let statement = if name.is_empty() {
                                        format!(
                                            "builder.entry(&RawString({key:?}), &arg);",
                                            key = key
                                        )
                                    } else {
                                        format!("builder.field({key:?}, &arg);", key = key)
                                    };

                                    builder_tokens
                                        .extend(TokenStream::from_str(&statement).unwrap());
                                }
                                None => {
                                    let statement = if name.is_empty() {
                                        format!(
                                        "builder.entry(&RawString({key:?}), &self.{field_name});",
                                        key = key,
                                        field_name = field_name
                                    )
                                    } else {
                                        format!(
                                            "builder.field({key:?}, &self.{field_name});",
                                            key = key,
                                            field_name = field_name
                                        )
                                    };

                                    builder_tokens
                                        .extend(TokenStream::from_str(&statement).unwrap());
                                }
                            }
                        }
                    }

                    has_fields = true;
                }
            }
        } else {
            builder_tokens.extend(quote!(let mut builder = formatter.debug_tuple(#name);));

            if let Data::Struct(data) = &ast.data {
                for (index, field) in data.fields.iter().enumerate() {
                    let field_attribute = FieldAttributeBuilder {
                        name: FieldAttributeName::Default,
                        enable_name: false,
                        enable_ignore: true,
                        enable_impl: true,
                    }
                    .from_attributes(&field.attrs, traits);

                    if field_attribute.ignore {
                        continue;
                    }

                    let format_trait = field_attribute.format_trait;
                    let format_method = field_attribute.format_method;

                    let field_name = if let Some(ident) = field.ident.as_ref() {
                        ident.to_string()
                    } else {
                        format!("{}", index)
                    };

                    match format_trait {
                        Some(format_trait) => {
                            let format_method = format_method.unwrap();

                            builder_tokens.extend(TokenStream::from_str(&format!("
                                let arg = {{
                                    struct MyDebug<'a, T: {format_trait}>(&'a T);

                                    impl<'a, T: {format_trait}> core::fmt::Debug for MyDebug<'a, T> {{
                                        fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                            {format_trait}::{format_method}(self.0, formatter)
                                        }}
                                    }}

                                    MyDebug(&self.{field_name})
                                }};
                            ", format_trait = format_trait, format_method = format_method, field_name = field_name)).unwrap());

                            builder_tokens
                                .extend(TokenStream::from_str("builder.field(&arg);").unwrap());
                        }
                        None => {
                            match format_method {
                                Some(format_method) => {
                                    let ty = field.ty.clone().into_token_stream().to_string();

                                    builder_tokens.extend(TokenStream::from_str(&format!("
                                        let arg = {{
                                            struct MyDebug<'a>(&'a {ty});

                                            impl<'a> core::fmt::Debug for MyDebug<'a> {{
                                                fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                    {format_method}(self.0, formatter)
                                                }}
                                            }}

                                            MyDebug(&self.{field_name})
                                        }};
                                    ", ty = ty, format_method = format_method, field_name = field_name)).unwrap());

                                    builder_tokens.extend(
                                        TokenStream::from_str("builder.field(&arg);").unwrap(),
                                    );
                                }
                                None => {
                                    let statement = format!(
                                        "builder.field(&self.{field_name});",
                                        field_name = field_name
                                    );

                                    builder_tokens
                                        .extend(TokenStream::from_str(&statement).unwrap());
                                }
                            }
                        }
                    }

                    has_fields = true;
                }
            }
        }

        if name.is_empty() && !has_fields {
            panic::unit_struct_need_name();
        }

        let ident = &ast.ident;

        let mut generics_cloned: Generics = ast.generics.clone();

        let where_clause = generics_cloned.make_where_clause();

        for where_predicate in bound {
            where_clause.predicates.push(where_predicate);
        }

        let (impl_generics, ty_generics, where_clause) = generics_cloned.split_for_impl();

        let debug_impl = quote! {
            impl #impl_generics core::fmt::Debug for #ident #ty_generics #where_clause {
                #[inline]
                fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    #builder_tokens
                    builder.finish()
                }
            }
        };

        tokens.extend(debug_impl);
    }
}
