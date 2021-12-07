use super::super::super::create_path_string_from_lit_str;

use crate::panic;
use crate::quote::ToTokens;
use crate::syn::{Attribute, Lit, Meta, NestedMeta};
use crate::Trait;

#[derive(Debug, Clone)]
pub enum FieldAttributeName {
    Default,
    Custom(String),
}

impl FieldAttributeName {
    pub fn into_option_string(self) -> Option<String> {
        match self {
            FieldAttributeName::Default => None,
            FieldAttributeName::Custom(s) => Some(s),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FieldAttribute {
    pub name: FieldAttributeName,
    pub ignore: bool,
    pub format_method: Option<String>,
    pub format_trait: Option<String>,
}

#[derive(Debug, Clone)]
pub struct FieldAttributeBuilder {
    pub name: FieldAttributeName,
    pub enable_name: bool,
    pub enable_ignore: bool,
    pub enable_impl: bool,
}

impl FieldAttributeBuilder {
    pub fn from_debug_meta(&self, meta: &Meta) -> FieldAttribute {
        let mut name = self.name.clone();

        let mut ignore = false;

        let mut format_method = None;
        let mut format_trait = None;

        let correct_usage_for_debug_attribute = {
            let mut usage = vec![];

            if self.enable_name {
                usage.push(stringify!(#[educe(Debug = "new_name")]));
                usage.push(stringify!(#[educe(Debug("new_name"))]));
            }

            if self.enable_ignore {
                usage.push(stringify!(#[educe(Debug = false)]));
                usage.push(stringify!(#[educe(Debug(false))]));
            }

            usage
        };

        let correct_usage_for_name = {
            let usage = vec![
                stringify!(#[educe(Debug(name = "new_name"))]),
                stringify!(#[educe(Debug(name("new_name")))]),
            ];

            usage
        };

        let correct_usage_for_ignore = {
            let usage = vec![stringify!(#[educe(Debug(ignore))])];

            usage
        };

        let correct_usage_for_impl = {
            let usage = vec![
                stringify!(#[educe(Debug(method = "path_to_method"))]),
                stringify!(#[educe(Debug(trait = "path_to_trait"))]),
                stringify!(#[educe(Debug(trait = "path_to_trait", method = "path_to_method_in_trait"))]),
                stringify!(#[educe(Debug(method("path_to_method")))]),
                stringify!(#[educe(Debug(trait("path_to_trait")))]),
                stringify!(#[educe(Debug(trait("path_to_trait"), method("path_to_method_in_trait")))]),
            ];

            usage
        };

        match meta {
            Meta::List(list) => {
                let mut name_is_set = false;
                let mut ignore_is_set = false;

                for p in list.nested.iter() {
                    match p {
                        NestedMeta::Meta(meta) => {
                            let meta_name = meta.path().into_token_stream().to_string();

                            match meta_name.as_str() {
                                "name" | "rename" => {
                                    if !self.enable_name {
                                        panic::unknown_parameter("Debug", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(lit) => {
                                                        match lit {
                                                            Lit::Str(s) => {
                                                                if name_is_set {
                                                                    panic::reset_parameter(
                                                                        meta_name.as_str(),
                                                                    );
                                                                }

                                                                name_is_set = true;

                                                                let s =
                                                                    create_path_string_from_lit_str(
                                                                        s,
                                                                    );

                                                                name = match s {
                                                                Some(s) => {
                                                                    FieldAttributeName::Custom(s)
                                                                }
                                                                None => {
                                                                    panic::disable_named_field_name(
                                                                    )
                                                                }
                                                            };
                                                            }
                                                            Lit::Bool(s) => {
                                                                if name_is_set {
                                                                    panic::reset_parameter(
                                                                        meta_name.as_str(),
                                                                    );
                                                                }

                                                                name_is_set = true;

                                                                if s.value {
                                                                    name =
                                                                        FieldAttributeName::Default;
                                                                } else {
                                                                    panic::disable_named_field_name(
                                                                    );
                                                                }
                                                            }
                                                            _ => {
                                                                panic::parameter_incorrect_format(
                                                                    meta_name.as_str(),
                                                                    &correct_usage_for_name,
                                                                )
                                                            }
                                                        }
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_name,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Str(s) => {
                                                    if name_is_set {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    name_is_set = true;

                                                    let s = create_path_string_from_lit_str(s);

                                                    name = match s {
                                                        Some(s) => FieldAttributeName::Custom(s),
                                                        None => panic::disable_named_field_name(),
                                                    };
                                                }
                                                Lit::Bool(s) => {
                                                    if name_is_set {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    name_is_set = true;

                                                    if s.value {
                                                        name = FieldAttributeName::Default;
                                                    } else {
                                                        panic::disable_named_field_name();
                                                    }
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_name,
                                                    )
                                                }
                                            }
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_name,
                                            )
                                        }
                                    }
                                }
                                "ignore" => {
                                    if !self.enable_ignore {
                                        panic::unknown_parameter("Debug", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::Path(_) => {
                                            if ignore_is_set {
                                                panic::reset_parameter(meta_name.as_str());
                                            }

                                            ignore_is_set = true;

                                            ignore = true;
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_ignore,
                                            )
                                        }
                                    }
                                }
                                "method" => {
                                    if !self.enable_impl {
                                        panic::unknown_parameter("Debug", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Str(s)) => {
                                                        if format_method.is_some() {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        let s = create_path_string_from_lit_str(s);

                                                        if let Some(s) = s {
                                                            format_method = Some(s);
                                                        } else {
                                                            panic::empty_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_impl,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Str(s) => {
                                                    if format_method.is_some() {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    let s = create_path_string_from_lit_str(s);

                                                    if let Some(s) = s {
                                                        format_method = Some(s);
                                                    } else {
                                                        panic::empty_parameter(meta_name.as_str());
                                                    }
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_impl,
                                                    )
                                                }
                                            }
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_impl,
                                            )
                                        }
                                    }
                                }
                                "trait" => {
                                    if !self.enable_impl {
                                        panic::unknown_parameter("Debug", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Str(s)) => {
                                                        if format_trait.is_some() {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        let s = create_path_string_from_lit_str(s);

                                                        if let Some(s) = s {
                                                            format_trait = Some(s);
                                                        } else {
                                                            panic::empty_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_impl,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Str(s) => {
                                                    if format_trait.is_some() {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    let s = create_path_string_from_lit_str(s);

                                                    if let Some(s) = s {
                                                        format_trait = Some(s);
                                                    } else {
                                                        panic::empty_parameter(meta_name.as_str());
                                                    }
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_impl,
                                                    )
                                                }
                                            }
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_impl,
                                            )
                                        }
                                    }
                                }
                                _ => panic::unknown_parameter("Debug", meta_name.as_str()),
                            }
                        }
                        NestedMeta::Lit(lit) => {
                            match lit {
                                Lit::Str(s) => {
                                    if !self.enable_name {
                                        panic::attribute_incorrect_format(
                                            "Debug",
                                            &correct_usage_for_debug_attribute,
                                        )
                                    }

                                    if name_is_set {
                                        panic::reset_parameter("name");
                                    }

                                    name_is_set = true;

                                    let s = create_path_string_from_lit_str(s);

                                    name = match s {
                                        Some(s) => FieldAttributeName::Custom(s),
                                        None => panic::disable_named_field_name(),
                                    };
                                }
                                Lit::Bool(b) => {
                                    if !self.enable_ignore {
                                        panic::attribute_incorrect_format(
                                            "Debug",
                                            &correct_usage_for_debug_attribute,
                                        )
                                    }

                                    if ignore_is_set {
                                        panic::reset_parameter("ignore");
                                    }

                                    ignore_is_set = true;

                                    ignore = !b.value;
                                }
                                _ => {
                                    panic::attribute_incorrect_format(
                                        "Debug",
                                        &correct_usage_for_debug_attribute,
                                    )
                                }
                            }
                        }
                    }
                }
            }
            Meta::NameValue(named_value) => {
                let lit = &named_value.lit;

                match lit {
                    Lit::Str(s) => {
                        if !self.enable_name {
                            panic::attribute_incorrect_format(
                                "Debug",
                                &correct_usage_for_debug_attribute,
                            )
                        }

                        let s = create_path_string_from_lit_str(s);

                        name = match s {
                            Some(s) => FieldAttributeName::Custom(s),
                            None => panic::disable_named_field_name(),
                        };
                    }
                    Lit::Bool(b) => {
                        if !self.enable_ignore {
                            panic::attribute_incorrect_format(
                                "Debug",
                                &correct_usage_for_debug_attribute,
                            )
                        }

                        ignore = !b.value;
                    }
                    _ => {
                        panic::attribute_incorrect_format(
                            "Debug",
                            &correct_usage_for_debug_attribute,
                        )
                    }
                }
            }
            _ => panic::attribute_incorrect_format("Debug", &correct_usage_for_debug_attribute),
        }

        if format_trait.is_some() && format_method.is_none() {
            format_method = Some("fmt".to_string());
        }

        FieldAttribute {
            name,
            ignore,
            format_method,
            format_trait,
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn from_attributes(self, attributes: &[Attribute], traits: &[Trait]) -> FieldAttribute {
        let mut result = None;

        for attribute in attributes.iter() {
            let meta = attribute.parse_meta().unwrap();

            let meta_name = meta.path().into_token_stream().to_string();

            if meta_name.as_str() == "educe" {
                match meta {
                    Meta::List(list) => {
                        for p in list.nested.iter() {
                            match p {
                                NestedMeta::Meta(meta) => {
                                    let meta_name = meta.path().into_token_stream().to_string();

                                    let t = Trait::from_str(meta_name);

                                    if traits.binary_search(&t).is_err() {
                                        panic::trait_not_used(t);
                                    }

                                    if t == Trait::Debug {
                                        if result.is_some() {
                                            panic::reuse_a_trait(t);
                                        }

                                        result = Some(self.from_debug_meta(meta));
                                    }
                                }
                                _ => panic::educe_format_incorrect(),
                            }
                        }
                    }
                    _ => panic::educe_format_incorrect(),
                }
            }
        }

        result.unwrap_or(FieldAttribute {
            name: self.name,
            ignore: false,
            format_method: None,
            format_trait: None,
        })
    }
}
