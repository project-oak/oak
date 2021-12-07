use crate::helpers::*;
use proc_macro2::*;
use proc_quote::*;
use syn::*;

pub mod filter_reflection;
pub mod parse;

/// Struct that contains information to generate the necessary code for `ParseFilter`.
struct ParseFilter<'a> {
    name: &'a Ident,
    meta: ParseFilterMeta,
    generics: &'a Generics,
}

impl<'a> ParseFilter<'a> {
    /// Generates `impl` declaration of the given trait for the structure
    /// represented by `self`.
    fn generate_impl(&self, trait_name: TokenStream) -> TokenStream {
        let name = &self.name;
        let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();
        quote! {
            impl #impl_generics #trait_name for #name #ty_generics #where_clause
        }
    }

    /// Asserts that this is an empty struct.
    fn validate_data(data: &Data) -> Result<()> {
        match data {
            Data::Struct(_) => Ok(()),
            Data::Enum(data) => Err(Error::new_spanned(
                data.enum_token,
                "Enums cannot be ParseFilter.",
            )),
            Data::Union(data) => Err(Error::new_spanned(
                data.union_token,
                "Unions cannot be ParseFilter.",
            )),
        }
    }

    /// Searches for `#[filter(...)]` in order to parse `ParseFilterMeta`.
    fn parse_attrs(attrs: &[Attribute]) -> Result<ParseFilterMeta> {
        let mut filter_attrs = attrs.iter().filter(|attr| attr.path.is_ident("filter"));

        match (filter_attrs.next(), filter_attrs.next()) {
            (Some(attr), None) => ParseFilterMeta::from_attr(attr),

            (_, Some(attr)) => Err(Error::new_spanned(
                attr,
                "Found multiple definitions for `filter` attribute.",
            )),

            _ => Err(Error::new(
                Span::call_site(),
                "Cannot find `filter` attribute in target struct. Have you tried adding `#[parser(name=\"...\", description=\"...\", parameters(...), parsed(...))]`?",
            )),
        }
    }

    /// Tries to create a new `ParseFilter` from the given `DeriveInput`
    fn from_input(input: &'a DeriveInput) -> Result<Self> {
        let DeriveInput {
            attrs,
            data,
            ident,
            generics,
            ..
        } = input;

        Self::validate_data(&data)?;
        let meta = Self::parse_attrs(attrs)?;

        Ok(ParseFilter {
            name: ident,
            meta,
            generics,
        })
    }
}

/// Struct that contains information parsed in `#[filter(...)]` attribute.
struct ParseFilterMeta {
    filter_name: Result<String>,
    filter_description: Result<String>,
    parameters_struct_name: Option<Ident>,
    filter_struct_name: Result<Ident>,
}

impl ParseFilterMeta {
    /// Tries to create a new `ParseFilterMeta` from the given `Attribute`
    fn from_attr(attr: &Attribute) -> Result<Self> {
        let meta = attr.parse_meta().map_err(|err| {
            Error::new(
                err.span(),
                format!("Could not parse `filter` attribute: {}", err),
            )
        })?;

        let meta = match meta {
            Meta::Path(meta) => return Err(Error::new_spanned(
                meta,
                "Found filter without name or description. Meta information is necessary in order to properly generate ParameterReflection.",
            )),
            Meta::NameValue(meta) => return Err(Error::new_spanned(
                meta,
                "Couldn't parse this parameter attribute. Have you tried `#[parser(name=\"...\", description=\"...\", parameters(...), parsed(...))]`?",
            )),
            Meta::List(meta) => meta,
        };

        let mut name = AssignOnce::Unset;
        let mut description = AssignOnce::Unset;
        let mut parameters = AssignOnce::Unset;
        let mut parsed = AssignOnce::Unset;

        for meta in meta.nested.into_iter() {
            match meta {
                NestedMeta::Meta(Meta::NameValue(meta)) => {
                    let key = &meta.path.get_ident().expect("Single element path");
                    let value = &meta.lit;

                    match key.to_string().as_str() {
                        "name" => assign_str_value(&mut name, key, value)?,
                        "description" => assign_str_value(&mut description, key, value)?,
                        "parameters" => {
                            return Err(Error::new_spanned(key, "Did you mean `parameters(...)`."));
                        }
                        "parsed" => {
                            return Err(Error::new_spanned(key, "Did you mean `parsed(...)`."));
                        }
                        _ => {
                            return Err(Error::new_spanned(
                                key,
                                "Unknown element in filter attribute.",
                            ));
                        }
                    }
                }

                NestedMeta::Meta(Meta::List(meta)) => {
                    let attr = &meta.path.get_ident().expect("Single element path");

                    let mut meta = meta.nested.into_iter();
                    match (meta.next(), meta.next()) {
                        (Some(meta), None) => {
                            if let NestedMeta::Meta(Meta::Path(meta)) = meta {
                                match attr.to_string().as_str() {
                                    "parameters" => assign_ident(
                                        &mut parameters,
                                        attr,
                                        meta.get_ident().expect("Single element path").clone(),
                                    )?,
                                    "parsed" => assign_ident(
                                        &mut parsed,
                                        attr,
                                        meta.get_ident().expect("Single element path").clone(),
                                    )?,
                                    _ => {
                                        return Err(Error::new_spanned(
                                            attr,
                                            "Unknown element in filter attribute.",
                                        ));
                                    }
                                }
                            } else {
                                return Err(Error::new_spanned(
                                    meta,
                                    "Unexpected element in filter attribute.",
                                ));
                            }
                        }
                        (_, Some(meta)) => {
                            return Err(Error::new_spanned(
                                meta,
                                "Unexpected element in filter attribute.",
                            ));
                        }
                        _ => {
                            return Err(Error::new_spanned(
                                attr,
                                "Element expected in filter attribute.",
                            ));
                        }
                    }
                }

                _ => {
                    return Err(Error::new_spanned(
                        meta,
                        "Unknown element in filter attribute.",
                    ));
                }
            }
        }

        let filter_name = name.unwrap_or_err(|| Error::new_spanned(
            attr,
            "FilterReflection does not have a name. Have you tried `#[filter(name=\"...\", description=\"...\", parameters(...), parsed(...))]`?",
        ));
        let filter_description = description.unwrap_or_err(|| Error::new_spanned(
            attr,
            "FilterReflection does not have a description. Have you tried `#[filter(name=\"...\", description=\"...\", parameters(...), parsed(...))]`?",
        ));
        let parameters_struct_name = parameters.into_option();
        let filter_struct_name = parsed.unwrap_or_err(|| Error::new_spanned(
            attr,
            "ParseFilter does not have a Filter to return. Have you tried `#[filter(name=\"...\", description=\"...\", parameters(...), parsed(...))]`?",
        ));

        Ok(ParseFilterMeta {
            filter_name,
            filter_description,
            parameters_struct_name,
            filter_struct_name,
        })
    }
}
