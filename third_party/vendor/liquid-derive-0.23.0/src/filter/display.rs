use crate::helpers::*;
use proc_macro2::*;
use proc_quote::*;
use syn::*;

/// Struct that contains information about the `Filter` struct to generate the
/// necessary code for `Display`.
struct FilterStruct<'a> {
    name: &'a Ident,
    filter_name: String,
    parameters: Option<Parameters<'a>>,
    generics: &'a Generics,
}

/// The field that holds `FilterParameters`.
enum Parameters<'a> {
    Ident(&'a Ident),
    Pos(usize),
}

impl<'a> Parameters<'a> {
    /// Creates a new `Parameters` from the given `ident` (if it is
    /// a struct with named fields) or the given position of the field
    /// (in case of unnamed parameters).
    fn new(ident: Option<&'a Ident>, pos: usize) -> Self {
        match ident {
            Some(ident) => Parameters::Ident(ident),
            None => Parameters::Pos(pos),
        }
    }
}

impl<'a> ToTokens for Parameters<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Parameters::Ident(ident) => ident.to_tokens(tokens),
            Parameters::Pos(pos) => pos.to_tokens(tokens),
        }
    }
}

impl<'a> FilterStruct<'a> {
    /// Generates `impl` declaration of the given trait for the structure
    /// represented by `self`.
    fn generate_impl(&self, trait_name: TokenStream) -> TokenStream {
        let name = &self.name;
        let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();
        quote! {
            impl #impl_generics #trait_name for #name #ty_generics #where_clause
        }
    }

    /// Searches for `#[name(...)]` in order to parse `filter_name`.
    fn parse_attrs(attrs: &[Attribute]) -> Result<String> {
        let mut evaluated_attrs = attrs.iter().filter(|attr| attr.path.is_ident("name"));

        match (evaluated_attrs.next(), evaluated_attrs.next()) {
            (Some(attr), None) => Self::parse_name_attr(attr),

            (_, Some(attr)) => Err(Error::new_spanned(
                attr,
                "Found multiple definitions for `name` attribute.",
            )),

            _ => Err(Error::new(
                Span::call_site(),
                "Cannot find `name` attribute in target struct. Have you tried adding `#[name = \"...\"]`?",
            )),
        }
    }

    /// Parses `#[name(...)]` attribute.
    fn parse_name_attr(attr: &Attribute) -> Result<String> {
        let meta = attr.parse_meta().map_err(|err| {
            Error::new(
                err.span(),
                format!("Could not parse `evaluated` attribute: {}", err),
            )
        })?;

        if let Meta::NameValue(meta) = meta {
            if let Lit::Str(name) = &meta.lit {
                Ok(name.value())
            } else {
                Err(Error::new_spanned(&meta.lit, "Expected string literal."))
            }
        } else {
            Err(Error::new_spanned(
                meta,
                "Couldn't parse evaluated attribute. Have you tried `#[evaluated(\"...\")]`?",
            ))
        }
    }

    /// Tries to create a new `FilterStruct` from the given `DeriveInput`
    fn from_input(input: &'a DeriveInput) -> Result<Self> {
        let DeriveInput {
            ident,
            generics,
            data,
            attrs,
            ..
        } = &input;
        let mut parameters = AssignOnce::Unset;

        let fields = match data {
            Data::Struct(data) => &data.fields,
            Data::Enum(data) => {
                return Err(Error::new_spanned(
                    data.enum_token,
                    "Filters cannot be `enum`s.",
                ));
            }
            Data::Union(data) => {
                return Err(Error::new_spanned(
                    data.union_token,
                    "Filters cannot be `union`s.",
                ));
            }
        };

        let marked = fields.iter().enumerate().filter(|(_, field)| {
            field
                .attrs
                .iter()
                .any(|attr| attr.path.is_ident("parameters"))
        });

        for (i, field) in marked {
            let params = Parameters::new(field.ident.as_ref(), i);
            parameters.set(params, || Error::new_spanned(
                field,
                "A previous field was already marked as `parameters`. Only one field can be marked as so.",
            ))?;
        }

        let name = ident;
        let filter_name = Self::parse_attrs(attrs)?;
        let parameters = parameters.into_option();

        Ok(Self {
            name,
            filter_name,
            parameters,
            generics,
        })
    }
}

/// Generates implementation of `Display`.
fn generate_impl_display(filter: &FilterStruct<'_>) -> TokenStream {
    let FilterStruct {
        filter_name,
        parameters,
        ..
    } = &filter;

    let impl_display = filter.generate_impl(quote! { ::std::fmt::Display });

    if let Some(parameters) = parameters {
        quote! {
            #impl_display {
                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                    ::std::write!(f, "{} : {}", #filter_name, &self.#parameters)
                }
            }
        }
    } else {
        quote! {
            #impl_display {
                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                    ::std::write!(f, "{}", #filter_name)
                }
            }
        }
    }
}

pub fn derive(input: &DeriveInput) -> TokenStream {
    let filter = match FilterStruct::from_input(input) {
        Ok(filter) => filter,
        Err(err) => return err.to_compile_error(),
    };

    generate_impl_display(&filter)
}
