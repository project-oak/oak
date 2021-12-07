use super::super::super::{
    create_where_predicates_from_generic_parameters, create_where_predicates_from_lit_str,
};

use crate::panic;
use crate::quote::ToTokens;
use crate::syn::{
    punctuated::Punctuated, token::Comma, Attribute, GenericParam, Lit, Meta, NestedMeta,
    WherePredicate,
};
use crate::Trait;

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
                    &syn::parse2(quote!(core::cmp::PartialOrd)).unwrap(),
                )
            }
            TypeAttributeBound::Custom(where_predicates) => where_predicates,
        }
    }
}

#[derive(Clone)]
pub struct TypeAttribute {
    pub flag: bool,
    pub bound: TypeAttributeBound,
    pub rank: isize,
}

#[derive(Debug, Clone)]
pub struct TypeAttributeBuilder {
    pub enable_flag: bool,
    pub enable_bound: bool,
    pub rank: isize,
    pub enable_rank: bool,
}

impl TypeAttributeBuilder {
    pub fn from_partial_ord_meta(&self, meta: &Meta) -> TypeAttribute {
        let mut flag = false;
        let mut bound = TypeAttributeBound::None;
        let mut rank = self.rank;

        let correct_usage_for_partial_ord_attribute = {
            let mut usage = vec![];

            if self.enable_flag {
                usage.push(stringify!(#[educe(PartialOrd)]));
            }

            usage
        };

        let correct_usage_for_bound = {
            let usage = vec![
                stringify!(#[educe(PartialOrd(bound))]),
                stringify!(#[educe(PartialOrd(bound = "where_predicates"))]),
                stringify!(#[educe(PartialOrd(bound("where_predicates")))]),
            ];

            usage
        };

        let correct_usage_for_rank = {
            let usage = vec![
                stringify!(#[educe(PartialOrd(rank = comparison_value))]),
                stringify!(#[educe(PartialOrd(rank(comparison_value)))]),
            ];

            usage
        };

        match meta {
            Meta::List(list) => {
                let mut bound_is_set = false;
                let mut rank_is_set = false;

                for p in list.nested.iter() {
                    match p {
                        NestedMeta::Meta(meta) => {
                            let meta_name = meta.path().into_token_stream().to_string();

                            match meta_name.as_str() {
                                "bound" => {
                                    if !self.enable_bound {
                                        panic::unknown_parameter("PartialOrd", meta_name.as_str());
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
                                "rank" => {
                                    if !self.enable_rank {
                                        panic::unknown_parameter("PartialOrd", meta_name.as_str());
                                    }

                                    match meta {
                                        Meta::List(list) => {
                                            for p in list.nested.iter() {
                                                match p {
                                                    NestedMeta::Lit(Lit::Int(i)) => {
                                                        if rank_is_set {
                                                            panic::reset_parameter(
                                                                meta_name.as_str(),
                                                            );
                                                        }

                                                        rank_is_set = true;

                                                        rank = i.base10_parse().unwrap();
                                                    }
                                                    _ => {
                                                        panic::parameter_incorrect_format(
                                                            meta_name.as_str(),
                                                            &correct_usage_for_rank,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                        Meta::NameValue(named_value) => {
                                            let lit = &named_value.lit;

                                            match lit {
                                                Lit::Int(i) => {
                                                    if rank_is_set {
                                                        panic::reset_parameter(meta_name.as_str());
                                                    }

                                                    rank_is_set = true;

                                                    rank = i.base10_parse().unwrap();
                                                }
                                                _ => {
                                                    panic::parameter_incorrect_format(
                                                        meta_name.as_str(),
                                                        &correct_usage_for_rank,
                                                    )
                                                }
                                            }
                                        }
                                        _ => {
                                            panic::parameter_incorrect_format(
                                                meta_name.as_str(),
                                                &correct_usage_for_rank,
                                            )
                                        }
                                    }
                                }
                                _ => panic::unknown_parameter("PartialOrd", meta_name.as_str()),
                            }
                        }
                        _ => {
                            panic::attribute_incorrect_format(
                                "PartialOrd",
                                &correct_usage_for_partial_ord_attribute,
                            )
                        }
                    }
                }
            }
            Meta::NameValue(_) => {
                panic::attribute_incorrect_format(
                    "PartialOrd",
                    &correct_usage_for_partial_ord_attribute,
                )
            }
            Meta::Path(_) => {
                if !self.enable_flag {
                    panic::attribute_incorrect_format(
                        "PartialOrd",
                        &correct_usage_for_partial_ord_attribute,
                    );
                }

                flag = true;
            }
        }

        TypeAttribute {
            flag,
            bound,
            rank,
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

                                        if t == Trait::PartialOrd {
                                            if result.is_some() {
                                                panic::reuse_a_trait(t);
                                            }

                                            result = Some(self.from_partial_ord_meta(meta));
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
            bound: TypeAttributeBound::None,
            rank: self.rank,
        })
    }
}
