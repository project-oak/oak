use std::fmt::Write;
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

pub struct DebugEnumHandler;

impl TraitHandler for DebugEnumHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_flag: true,
            name: TypeAttributeName::Disable,
            enable_name: true,
            named_field: false,
            enable_named_field: false,
            enable_bound: true,
        }
        .from_debug_meta(meta);

        let enum_name = ast.ident.to_string();

        let name = type_attribute.name.into_string_by_ident(&ast.ident);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut builder_tokens = TokenStream::new();
        let mut has_variants = false;

        let mut match_tokens = String::from("match self {");

        if let Data::Enum(data) = &ast.data {
            for variant in data.variants.iter() {
                let type_attribute = TypeAttributeBuilder {
                    enable_flag: false,
                    name: TypeAttributeName::Default,
                    enable_name: true,
                    named_field: matches!(&variant.fields, Fields::Named(_)),
                    enable_named_field: true,
                    enable_bound: false,
                }
                .from_attributes(&variant.attrs, traits);

                let variant_name = type_attribute.name.into_string_by_ident(&variant.ident);

                let named_field = type_attribute.named_field;

                let variant_ident = variant.ident.to_string();

                let name = combine_names(&name, variant_name);

                match &variant.fields {
                    Fields::Unit => {
                        // TODO Unit
                        if name.is_empty() {
                            panic::unit_variant_need_name();
                        }

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident} => {{ formatter.write_str({name:?}) }}", enum_name = enum_name, variant_ident = variant_ident, name = name)).unwrap();

                        has_variants = true;
                    }
                    Fields::Named(fields) => {
                        // TODO Struct
                        let mut has_fields = false;

                        let mut pattern_tokens = String::new();
                        let mut block_tokens = String::new();

                        if named_field {
                            if name.is_empty() {
                                block_tokens.push_str("
                                    struct RawString(&'static str);

                                    impl core::fmt::Debug for RawString {{
                                        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {{
                                            f.write_str(self.0)
                                        }}
                                    }}
                                ");

                                block_tokens.push_str("let mut builder = formatter.debug_map();");
                            } else {
                                block_tokens
                                    .write_fmt(format_args!(
                                        "let mut builder = formatter.debug_struct({name:?});",
                                        name = name
                                    ))
                                    .unwrap();
                            }

                            for field in fields.named.iter() {
                                let field_attribute = FieldAttributeBuilder {
                                    name: FieldAttributeName::Default,
                                    enable_name: true,
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
                                    continue;
                                }

                                let rename = field_attribute.name.into_option_string();

                                let format_trait = field_attribute.format_trait;
                                let format_method = field_attribute.format_method;

                                let key = rename.unwrap_or_else(|| field_name.clone());

                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                match format_trait {
                                    Some(format_trait) => {
                                        let format_method = format_method.unwrap();

                                        block_tokens.write_fmt(format_args!("
                                            let arg = {{
                                                struct MyDebug<'a, T: {format_trait}>(&'a T);

                                                impl<'a, T: {format_trait}> core::fmt::Debug for MyDebug<'a, T> {{
                                                    fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                        {format_trait}::{format_method}(self.0, formatter)
                                                    }}
                                                }}

                                                MyDebug({field_name})
                                            }};
                                        ", format_trait = format_trait, format_method = format_method, field_name = field_name)).unwrap();

                                        let statement = if name.is_empty() {
                                            format!(
                                                "builder.entry(&RawString({key:?}), &arg);",
                                                key = key
                                            )
                                        } else {
                                            format!("builder.field({key:?}, &arg);", key = key)
                                        };

                                        block_tokens.push_str(&statement);
                                    }
                                    None => {
                                        match format_method {
                                            Some(format_method) => {
                                                let ty = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                block_tokens.write_fmt(format_args!("
                                                    let arg = {{
                                                        struct MyDebug<'a>(&'a {ty});

                                                        impl<'a> core::fmt::Debug for MyDebug<'a> {{
                                                            fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                                {format_method}(self.0, formatter)
                                                            }}
                                                        }}

                                                        MyDebug({field_name})
                                                    }};
                                                ", ty = ty, format_method = format_method, field_name = field_name)).unwrap();

                                                let statement = if name.is_empty() {
                                                    format!(
                                                        "builder.entry(&RawString({key:?}), &arg);",
                                                        key = key
                                                    )
                                                } else {
                                                    format!(
                                                        "builder.field({key:?}, &arg);",
                                                        key = key
                                                    )
                                                };

                                                block_tokens.push_str(&statement);
                                            }
                                            None => {
                                                let statement = if name.is_empty() {
                                                    format!("builder.entry(&RawString({key:?}), {field_name});", key = key, field_name = field_name)
                                                } else {
                                                    format!(
                                                        "builder.field({key:?}, {field_name});",
                                                        key = key,
                                                        field_name = field_name
                                                    )
                                                };

                                                block_tokens.push_str(&statement);
                                            }
                                        }
                                    }
                                }

                                has_fields = true;
                            }
                        } else {
                            block_tokens
                                .write_fmt(format_args!(
                                    "let mut builder = formatter.debug_tuple({name:?});",
                                    name = name
                                ))
                                .unwrap();

                            for field in fields.named.iter() {
                                let field_attribute = FieldAttributeBuilder {
                                    name: FieldAttributeName::Default,
                                    enable_name: false,
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
                                    continue;
                                }

                                let format_trait = field_attribute.format_trait;
                                let format_method = field_attribute.format_method;

                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                match format_trait {
                                    Some(format_trait) => {
                                        let format_method = format_method.unwrap();

                                        block_tokens.write_fmt(format_args!("
                                            let arg = {{
                                                struct MyDebug<'a, T: {format_trait}>(&'a T);

                                                impl<'a, T: {format_trait}> core::fmt::Debug for MyDebug<'a, T> {{
                                                    fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                        {format_trait}::{format_method}(self.0, formatter)
                                                    }}
                                                }}

                                                MyDebug({field_name})
                                            }};
                                        ", format_trait = format_trait, format_method = format_method, field_name = field_name)).unwrap();

                                        block_tokens.push_str("builder.field(&arg);");
                                    }
                                    None => {
                                        match format_method {
                                            Some(format_method) => {
                                                let ty = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                block_tokens.write_fmt(format_args!("
                                                    let arg = {{
                                                        struct MyDebug<'a>(&'a {ty});

                                                        impl<'a> core::fmt::Debug for MyDebug<'a> {{
                                                            fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                                {format_method}(self.0, formatter)
                                                            }}
                                                        }}

                                                        MyDebug({field_name})
                                                    }};
                                                ", ty = ty, format_method = format_method, field_name = field_name)).unwrap();

                                                block_tokens.push_str("builder.field(&arg);");
                                            }
                                            None => {
                                                let statement = format!(
                                                    "builder.field({field_name});",
                                                    field_name = field_name
                                                );

                                                block_tokens.push_str(&statement);
                                            }
                                        }
                                    }
                                }

                                has_fields = true;
                            }
                        }

                        if name.is_empty() && !has_fields {
                            panic::unit_struct_need_name();
                        }

                        block_tokens.push_str("return builder.finish();");

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}{{ {pattern_tokens} }} => {{ {block_tokens} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, block_tokens = block_tokens)).unwrap();

                        has_variants = true;
                    }
                    Fields::Unnamed(fields) => {
                        // TODO Tuple
                        let mut has_fields = false;

                        let mut pattern_tokens = String::new();
                        let mut block_tokens = String::new();

                        if named_field {
                            if name.is_empty() {
                                block_tokens.push_str("
                                    struct RawString(&'static str);

                                    impl core::fmt::Debug for RawString {{
                                        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {{
                                            f.write_str(self.0)
                                        }}
                                    }}
                                ");

                                block_tokens.push_str("let mut builder = formatter.debug_map();");
                            } else {
                                block_tokens
                                    .write_fmt(format_args!(
                                        "let mut builder = formatter.debug_struct({name:?});",
                                        name = name
                                    ))
                                    .unwrap();
                            }

                            for (index, field) in fields.unnamed.iter().enumerate() {
                                let field_attribute = FieldAttributeBuilder {
                                    name: FieldAttributeName::Default,
                                    enable_name: true,
                                    enable_ignore: true,
                                    enable_impl: true,
                                }
                                .from_attributes(&field.attrs, traits);

                                if field_attribute.ignore {
                                    pattern_tokens.push_str("_,");
                                    continue;
                                }

                                let rename = field_attribute.name.into_option_string();

                                let format_trait = field_attribute.format_trait;
                                let format_method = field_attribute.format_method;

                                let (key, field_name) = match rename {
                                    Some(rename) => (rename, format!("{}", index)),
                                    None => (format!("_{}", index), format!("{}", index)),
                                };

                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "_{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                match format_trait {
                                    Some(format_trait) => {
                                        let format_method = format_method.unwrap();

                                        block_tokens.write_fmt(format_args!("
                                            let arg = {{
                                                struct MyDebug<'a, T: {format_trait}>(&'a T);

                                                impl<'a, T: {format_trait}> core::fmt::Debug for MyDebug<'a, T> {{
                                                    fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                        {format_trait}::{format_method}(self.0, formatter)
                                                    }}
                                                }}

                                                MyDebug(_{field_name})
                                            }};
                                        ", format_trait = format_trait, format_method = format_method, field_name = field_name)).unwrap();

                                        let statement = if name.is_empty() {
                                            format!(
                                                "builder.entry(&RawString({key:?}), &arg);",
                                                key = key
                                            )
                                        } else {
                                            format!("builder.field({key:?}, &arg);", key = key)
                                        };

                                        block_tokens.push_str(&statement);
                                    }
                                    None => {
                                        match format_method {
                                            Some(format_method) => {
                                                let ty = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                block_tokens.write_fmt(format_args!("
                                                    let arg = {{
                                                        struct MyDebug<'a>(&'a {ty});

                                                        impl<'a> core::fmt::Debug for MyDebug<'a> {{
                                                            fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                                {format_method}(self.0, formatter)
                                                            }}
                                                        }}

                                                        MyDebug(_{field_name})
                                                    }};
                                                ", ty = ty, format_method = format_method, field_name = field_name)).unwrap();

                                                let statement = if name.is_empty() {
                                                    format!(
                                                        "builder.entry(&RawString({key:?}), &arg);",
                                                        key = key
                                                    )
                                                } else {
                                                    format!(
                                                        "builder.field({key:?}, &arg);",
                                                        key = key
                                                    )
                                                };

                                                block_tokens.push_str(&statement);
                                            }
                                            None => {
                                                let statement = if name.is_empty() {
                                                    format!("builder.entry(&RawString({key:?}), {field_name});", key = key, field_name = field_name)
                                                } else {
                                                    format!(
                                                        "builder.field({key:?}, _{field_name});",
                                                        key = key,
                                                        field_name = field_name
                                                    )
                                                };

                                                block_tokens.push_str(&statement);
                                            }
                                        }
                                    }
                                }

                                has_fields = true;
                            }
                        } else {
                            block_tokens
                                .write_fmt(format_args!(
                                    "let mut builder = formatter.debug_tuple({name:?});",
                                    name = name
                                ))
                                .unwrap();

                            for (index, field) in fields.unnamed.iter().enumerate() {
                                let field_attribute = FieldAttributeBuilder {
                                    name: FieldAttributeName::Default,
                                    enable_name: false,
                                    enable_ignore: true,
                                    enable_impl: true,
                                }
                                .from_attributes(&field.attrs, traits);

                                if field_attribute.ignore {
                                    pattern_tokens.push_str("_,");
                                    continue;
                                }

                                let format_trait = field_attribute.format_trait;
                                let format_method = field_attribute.format_method;

                                let field_name = format!("{}", index);

                                pattern_tokens
                                    .write_fmt(format_args!(
                                        "_{field_name},",
                                        field_name = field_name
                                    ))
                                    .unwrap();

                                match format_trait {
                                    Some(format_trait) => {
                                        let format_method = format_method.unwrap();

                                        block_tokens.write_fmt(format_args!("
                                            let arg = {{
                                                struct MyDebug<'a, T: {format_trait}>(&'a T);

                                                impl<'a, T: {format_trait}> core::fmt::Debug for MyDebug<'a, T> {{
                                                    fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                        {format_trait}::{format_method}(self.0, formatter)
                                                    }}
                                                }}

                                                MyDebug(_{field_name})
                                            }};
                                        ", format_trait = format_trait, format_method = format_method, field_name = field_name)).unwrap();

                                        block_tokens.push_str("builder.field(&arg);");
                                    }
                                    None => {
                                        match format_method {
                                            Some(format_method) => {
                                                let ty = field
                                                    .ty
                                                    .clone()
                                                    .into_token_stream()
                                                    .to_string();

                                                block_tokens.write_fmt(format_args!("
                                                    let arg = {{
                                                        struct MyDebug<'a>(&'a {ty});

                                                        impl<'a> core::fmt::Debug for MyDebug<'a> {{
                                                            fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {{
                                                                {format_method}(self.0, formatter)
                                                            }}
                                                        }}

                                                        MyDebug(_{field_name})
                                                    }};
                                                ", ty = ty, format_method = format_method, field_name = field_name)).unwrap();

                                                block_tokens.push_str("builder.field(&arg);");
                                            }
                                            None => {
                                                let statement = format!(
                                                    "builder.field(_{field_name});",
                                                    field_name = field_name
                                                );

                                                block_tokens.push_str(&statement);
                                            }
                                        }
                                    }
                                }

                                has_fields = true;
                            }
                        }

                        if name.is_empty() && !has_fields {
                            panic::unit_struct_need_name();
                        }

                        block_tokens.push_str("return builder.finish();");

                        match_tokens.write_fmt(format_args!("{enum_name}::{variant_ident}( {pattern_tokens} ) => {{ {block_tokens} }}", enum_name = enum_name, variant_ident = variant_ident, pattern_tokens = pattern_tokens, block_tokens = block_tokens)).unwrap();

                        has_variants = true;
                    }
                }
            }
        }

        match_tokens.push('}');

        builder_tokens.extend(TokenStream::from_str(&match_tokens).unwrap());

        if name.is_empty() && !has_variants {
            panic::unit_enum_need_name();
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
                #[allow(clippy::unneeded_field_pattern)]
                fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    #builder_tokens
                }
            }
        };

        tokens.extend(debug_impl);
    }
}

fn combine_names(name: &str, variant_name: String) -> String {
    if name.is_empty() {
        if variant_name.is_empty() {
            String::new()
        } else {
            variant_name
        }
    } else {
        let mut name = name.to_string();

        if !variant_name.is_empty() {
            if !variant_name.starts_with("::") {
                name.push_str("::");
            }

            name.push_str(&variant_name);
        }

        name
    }
}
