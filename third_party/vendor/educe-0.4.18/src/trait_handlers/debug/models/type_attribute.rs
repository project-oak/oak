use super::super::super::{
    create_path_string_from_lit_str, create_where_predicates_from_generic_parameters,
    create_where_predicates_from_lit_str,
};

use crate::panic;
use crate::quote::ToTokens;
use crate::syn::{
    punctuated::Punctuated, token::Comma, Attribute, GenericParam, Ident, Lit, Meta, NestedMeta,
    WherePredicate,
};
use crate::Trait;

#[derive(Debug, Clone)]
pub enum TypeAttributeName {
    Disable,
    Default,
    Custom(String),
}

impl TypeAttributeName {
    pub fn into_string_by_ident(self, ident: &Ident) -> String {
        match self {
            TypeAttributeName::Disable => String::new(),
            TypeAttributeName::Default => ident.to_string(),
            TypeAttributeName::Custom(s) => s,
        }
    }
}

#[derive(Clone)]
pub enum TypeAttributeBound {
    None,
    Auto,
    Custom(Punctuated<WherePredicate, Comma>),
}

impl TypeAttributeBound {
    pub fn into_punctuated_where_predicates_by_generic_parameters(
        self,
        params: &Punctuated<GenericParam, Comma>,
    ) -> Punctuated<WherePredicate, Comma> {
        match self {
            TypeAttributeBound::None => Punctuated::new(),
            TypeAttributeBound::Auto => {
                create_where_predicates_from_generic_parameters(
                    params,
                    &syn::parse2(quote!(core::fmt::Debug)).unwrap(),
                )
            }
            TypeAttributeBound::Custom(where_predicates) => where_predicates,
        }
    }
}

#[derive(Clone)]
pub struct TypeAttribute {
    pub flag: bool,
    pub name: TypeAttributeName,
    pub named_field: bool,
    pub bound: TypeAttributeBound,
}

#[derive(Debug, Clone)]
pub struct TypeAttributeBuilder {
    pub enable_flag: bool,
    pub name: TypeAttributeName,
    pub enable_name: bool,
    pub named_field: bool,
    pub enable_named_field: bool,
    pub enable_bound: bool,
}

impl TypeAttributeBuilder {
    pub fn from_debug_meta(&self, meta: &Meta) -> TypeAttribute {
        let mut flag = false;
        let mut name = self.name.clone();
        let mut named_field = self.named_field;
        let mut bound = TypeAttributeBound::None;

        let correct_usage_for_debug_attribute = {
            let mut usage = vec![];

            if self.enable_flag {
                usage.push(stringify!(#[educe(Default)]));
            }

            if self.enable_name {
                usage.push(stringify!(#[educe(Debug = "new_name")]));
                usage.push(stringify!(#[educe(Debug("new_name"))]));
            }

            if self.enable_bound {
                usage.push(stringify!(#[educe(Debug(ignore))]));
            }

            usage
        };

        let correct_usage_for_name = {
            let mut usage = vec![
                stringify!(#[educe(Debug(name = "new_name"))]),
                stringify!(#[educe(Debug(name("new_name")))]),
            ];

            if let TypeAttributeName::Disable = &name {
                usage.push(stringify!(#[educe(Debug(name = true))]));
                usage.push(stringify!(#[educe(Debug(name(true)))]));
            } else {
                usage.push(stringify!(#[educe(Debug(name = false))]));
                usage.push(stringify!(#[educe(Debug(name(false)))]));
            }

            usage
        };

        let correct_usage_for_named_field = {
            let mut usage = vec![];

            if !self.named_field {
                usage.push(stringify!(#[educe(Debug(named_field = true))]));
                usage.push(stringify!(#[educe(Debug(named_field(true)))]));
            } else {
                usage.push(stringify!(#[educe(Debug(named_field = false))]));
                usage.push(stringify!(#[educe(Debug(named_field(false)))]));
            }

            usage
        };

        let correct_usage_for_bound = {
            let usage = vec![
                stringify!(#[educe(Debug(bound))]),
                stringify!(#[educe(Debug(bound = "where_predicates"))]),
                stringify!(#[educe(Debug(bound("where_predicates")))]),
            ];

            usage
        };

        match meta {
            Meta::List(list) => {
                let mut name_is_set = false;
                let mut named_field_is_set = false;
                let mut bound_is_set = false;

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
                                                                        TypeAttributeName::Custom(s)
                                                                    }
                                                                    None => {
                                                                        TypeAttributeName::Disable
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
                                                                        TypeAttributeName::Default;
                                                                } else {
                                                                    name =
                                                                        TypeAttributeName::Disable;
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
                                                        Some(s) => TypeAttributeName::Custom(s),
                                                        None => TypeAttributeName::Disable,
                                                    };
                                                }
                                                Lit::Bool(s) => {
                                                    if name_is_set {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    name_is_set = true;

                                                    if s.value {
                                                        name = TypeAttributeName::Default;
                                                    } else {
                                                        name = TypeAttributeName::Disable;
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
                                "named_field" => {
                                    if !self.enable_named_field {
                                        panic::unknown_parameter("Debug", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Bool(s)) => {
                                                        if named_field_is_set {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        named_field_is_set = true;

                                                        named_field = s.value;
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_named_field,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Bool(s) => {
                                                    if named_field_is_set {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    named_field_is_set = true;

                                                    named_field = s.value;
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_named_field,
                                                    )
                                                }
                                            }
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_named_field,
                                            )
                                        }
                                    }
                                }
                                "bound" => {
                                    if !self.enable_bound {
                                        panic::unknown_parameter("Debug", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Str(s)) => {
                                                        if bound_is_set {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        bound_is_set = true;

                                                        let where_predicates =
                                                            create_where_predicates_from_lit_str(s);

                                                        bound = match where_predicates {
                                                            Some(where_predicates) => {
                                                                TypeAttributeBound::Custom(
                                                                    where_predicates,
                                                                )
                                                            }
                                                            None => {
                                                                panic::empty_parameter(
                                                                    meta_name.as_str(),
                                                                )
                                                            }
                                                        };
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_bound,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Str(s) => {
                                                    if bound_is_set {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    bound_is_set = true;

                                                    let where_predicates =
                                                        create_where_predicates_from_lit_str(s);

                                                    bound = match where_predicates {
                                                        Some(where_predicates) => {
                                                            TypeAttributeBound::Custom(
                                                                where_predicates,
                                                            )
                                                        }
                                                        None => {
                                                            panic::empty_parameter(
                                                                meta_name.as_str(),
                                                            )
                                                        }
                                                    };
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_bound,
                                                    )
                                                }
                                            }
                                        }
                                        Meta::Path(_) => {
                                            if bound_is_set {
                                                panic::reset_parameter(meta_name.as_str());
                                            }

                                            bound_is_set = true;

                                            bound = TypeAttributeBound::Auto;
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
                                        Some(s) => TypeAttributeName::Custom(s),
                                        None => TypeAttributeName::Disable,
                                    };
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
                            Some(s) => TypeAttributeName::Custom(s),
                            None => TypeAttributeName::Disable,
                        };
                    }
                    _ => {
                        panic::attribute_incorrect_format(
                            "Debug",
                            &correct_usage_for_debug_attribute,
                        )
                    }
                }
            }
            Meta::Path(_) => {
                if !self.enable_flag {
                    panic::attribute_incorrect_format("Debug", &correct_usage_for_debug_attribute);
                }

                flag = true;
            }
        }

        TypeAttribute {
            flag,
            name,
            named_field,
            bound,
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn from_attributes(self, attributes: &[Attribute], traits: &[Trait]) -> TypeAttribute {
        let mut result = None;

        for attribute in attributes.iter() {
            if let Some(meta_name) = attribute.path.get_ident() {
                if meta_name == "educe" {
                    let meta = attribute.parse_meta().unwrap();

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
        }

        result.unwrap_or(TypeAttribute {
            flag: false,
            name: self.name,
            named_field: self.named_field,
            bound: TypeAttributeBound::None,
        })
    }
}
