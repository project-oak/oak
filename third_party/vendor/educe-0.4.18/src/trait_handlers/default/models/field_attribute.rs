use super::super::super::create_expr_string_from_lit_str;

use crate::panic;
use crate::quote::ToTokens;
use crate::syn::{Attribute, Lit, Meta, NestedMeta};
use crate::Trait;

#[derive(Clone)]
pub struct FieldAttribute {
    pub flag: bool,
    pub literal: Option<Lit>,
    pub expression: Option<String>,
}

#[derive(Debug, Clone)]
pub struct FieldAttributeBuilder {
    pub enable_flag: bool,
    pub enable_literal: bool,
    pub enable_expression: bool,
}

impl FieldAttributeBuilder {
    pub fn from_default_meta(&self, meta: &Meta) -> FieldAttribute {
        let mut flag = false;
        let mut value: Option<Lit> = None;
        let mut expression: Option<String> = None;

        let correct_usage_for_default_attribute = {
            let mut usage = vec![];

            if self.enable_flag {
                usage.push(stringify!(#[educe(Default)]));
            }

            if self.enable_literal {
                usage.push(stringify!(#[educe(Default = literal)]));
                usage.push(stringify!(#[educe(Default(literal))]));
            }

            usage
        };

        let correct_usage_for_expression = {
            let usage = vec![
                stringify!(#[educe(Default(expression = "expression"))]),
                stringify!(#[educe(Default(expression("expression")))]),
            ];

            usage
        };

        match meta {
            Meta::List(list) => {
                for p in list.nested.iter() {
                    match p {
                        NestedMeta::Meta(meta) => {
                            let meta_name = meta.path().into_token_stream().to_string();

                            match meta_name.as_str() {
                                "expression" | "expr" => {
                                    if !self.enable_expression {
                                        panic::unknown_parameter("Default", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Str(s)) => {
                                                        if expression.is_some() {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        let s = create_expr_string_from_lit_str(s);

                                                        if s.is_some() {
                                                            expression = s;
                                                        } else {
                                                            panic::empty_parameter(
                                                                meta_name.as_str(),
                                                            )
                                                        }
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_expression,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Str(s) => {
                                                    if expression.is_some() {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    let s = create_expr_string_from_lit_str(s);

                                                    if s.is_some() {
                                                        expression = s;
                                                    } else {
                                                        panic::empty_parameter(meta_name.as_str())
                                                    }
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_expression,
                                                    )
                                                }
                                            }
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_expression,
                                            )
                                        }
                                    }
                                }
                                _ => panic::unknown_parameter("Default", meta_name.as_str()),
                            }
                        }
                        NestedMeta::Lit(lit) => {
                            if !self.enable_literal {
                                panic::attribute_incorrect_format(
                                    "Default",
                                    &correct_usage_for_default_attribute,
                                )
                            }

                            if value.is_some() {
                                panic::reset_parameter("value");
                            }

                            value = Some(lit.clone());
                        }
                    }
                }
            }
            Meta::NameValue(named_value) => {
                if !self.enable_literal {
                    panic::attribute_incorrect_format(
                        "Default",
                        &correct_usage_for_default_attribute,
                    )
                }

                let lit = &named_value.lit;

                value = Some(lit.clone());
            }
            Meta::Path(_) => {
                if !self.enable_flag {
                    panic::attribute_incorrect_format(
                        "Default",
                        &correct_usage_for_default_attribute,
                    );
                }

                flag = true;
            }
        }

        if value.is_some() && expression.is_some() {
            panic::set_value_expression();
        }

        FieldAttribute {
            flag,
            literal: value,
            expression,
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

                                    if t == Trait::Default {
                                        if result.is_some() {
                                            panic::reuse_a_trait(t);
                                        }

                                        result = Some(self.from_default_meta(meta));
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
            flag: false,
            literal: None,
            expression: None,
        })
    }
}
