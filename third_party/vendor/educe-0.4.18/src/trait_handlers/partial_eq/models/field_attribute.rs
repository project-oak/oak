use super::super::super::create_path_string_from_lit_str;

use crate::panic;
use crate::quote::ToTokens;
use crate::syn::{Attribute, Lit, Meta, NestedMeta};
use crate::Trait;

#[derive(Debug, Clone)]
pub struct FieldAttribute {
    pub ignore: bool,
    pub compare_method: Option<String>,
    pub compare_trait: Option<String>,
}

#[derive(Debug, Clone)]
pub struct FieldAttributeBuilder {
    pub enable_ignore: bool,
    pub enable_impl: bool,
}

impl FieldAttributeBuilder {
    pub fn from_partial_eq_meta(&self, meta: &Meta) -> FieldAttribute {
        let mut ignore = false;

        let mut compare_method = None;
        let mut compare_trait = None;

        let correct_usage_for_partial_eq_attribute = {
            let mut usage = vec![];

            if self.enable_ignore {
                usage.push(stringify!(#[educe(PartialEq = false)]));
                usage.push(stringify!(#[educe(PartialEq(false))]));
            }

            usage
        };

        let correct_usage_for_ignore = {
            let usage = vec![stringify!(#[educe(PartialEq(ignore))])];

            usage
        };

        let correct_usage_for_impl = {
            let usage = vec![
                stringify!(#[educe(PartialEq(method = "path_to_method"))]),
                stringify!(#[educe(PartialEq(trait = "path_to_trait"))]),
                stringify!(#[educe(PartialEq(trait = "path_to_trait", method = "path_to_method_in_trait"))]),
                stringify!(#[educe(PartialEq(method("path_to_method")))]),
                stringify!(#[educe(PartialEq(trait("path_to_trait")))]),
                stringify!(#[educe(PartialEq(trait("path_to_trait"), method("path_to_method_in_trait")))]),
            ];

            usage
        };

        match meta {
            Meta::List(list) => {
                let mut ignore_is_set = false;

                for p in list.nested.iter() {
                    match p {
                        NestedMeta::Meta(meta) => {
                            let meta_name = meta.path().into_token_stream().to_string();

                            match meta_name.as_str() {
                                "ignore" => {
                                    if !self.enable_ignore {
                                        panic::unknown_parameter("PartialEq", meta_name.as_str());
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
                                        panic::unknown_parameter("PartialEq", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Str(s)) => {
                                                        if compare_method.is_some() {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        let s = create_path_string_from_lit_str(s);

                                                        if let Some(s) = s {
                                                            compare_method = Some(s);
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
                                                    if compare_method.is_some() {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    let s = create_path_string_from_lit_str(s);

                                                    if let Some(s) = s {
                                                        compare_method = Some(s);
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
                                        panic::unknown_parameter("PartialEq", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Str(s)) => {
                                                        if compare_trait.is_some() {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        let s = create_path_string_from_lit_str(s);

                                                        if let Some(s) = s {
                                                            compare_trait = Some(s);
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
                                                    if compare_trait.is_some() {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    let s = create_path_string_from_lit_str(s);

                                                    if let Some(s) = s {
                                                        compare_trait = Some(s);
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
                                _ => panic::unknown_parameter("PartialEq", meta_name.as_str()),
                            }
                        }
                        _ => {
                            panic::attribute_incorrect_format(
                                "PartialEq",
                                &correct_usage_for_partial_eq_attribute,
                            )
                        }
                    }
                }
            }
            _ => {
                panic::attribute_incorrect_format(
                    "PartialEq",
                    &correct_usage_for_partial_eq_attribute,
                )
            }
        }

        if compare_trait.is_some() && compare_method.is_none() {
            compare_method = Some("eq".to_string());
        }

        FieldAttribute {
            ignore,
            compare_method,
            compare_trait,
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

                                    if t == Trait::PartialEq {
                                        if result.is_some() {
                                            panic::reuse_a_trait(t);
                                        }

                                        result = Some(self.from_partial_eq_meta(meta));
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
            ignore: false,
            compare_method: None,
            compare_trait: None,
        })
    }
}
