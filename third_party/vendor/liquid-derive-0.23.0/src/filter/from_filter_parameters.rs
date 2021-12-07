use crate::helpers::*;
use proc_macro2::*;
use proc_quote::*;
use syn::*;

/// Struct that contains information about the `Filter` struct to generate the
/// necessary code for `From`.
struct FilterStruct<'a> {
    name: &'a Ident,
    parameters_struct_name: &'a Type,
    fields: Vec<FilterStructField<'a>>,
    ty: StructFieldsType,
    generics: &'a Generics,
}

/// The type of the fields of this struct.
enum StructFieldsType {
    Named,
    Unnamed,
    Unit,
}

impl StructFieldsType {
    /// Returns the type of the given Fields.
    fn from_fields(fields: &Fields) -> Self {
        match fields {
            Fields::Named(_) => StructFieldsType::Named,
            Fields::Unnamed(_) => StructFieldsType::Unnamed,
            Fields::Unit => StructFieldsType::Unit,
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

    /// Tries to create a new `FilterStruct` from the given `DeriveInput`
    fn from_input(input: &'a DeriveInput) -> Result<Self> {
        let DeriveInput {
            ident,
            generics,
            data,
            ..
        } = &input;
        let mut parameters_struct_name = AssignOnce::Unset;
        let mut filter_fields = Vec::new();

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

        let ty = StructFieldsType::from_fields(&fields);

        for field in fields.iter() {
            let filter_field = FilterStructField::from_field(field);
            if filter_field.is_filter_parameters() {
                parameters_struct_name.set(&field.ty, || Error::new_spanned(
                    field,
                    "A previous field was already marked as `parameters`. Only one field can be marked as so.",
                ))?;
            }
            filter_fields.push(filter_field);
        }

        let name = ident;
        let fields = filter_fields;
        let parameters_struct_name = parameters_struct_name.unwrap_or_err(|| Error::new(
            Span::call_site(),
            "Cannot find `FilterParameters` field in target struct. Mark this field with the `#[parameters]` attribute.",
        ))?;

        Ok(Self {
            name,
            fields,
            parameters_struct_name,
            ty,
            generics,
        })
    }
}

/// A field in `FilterStruct`. It can either be a regular one or the one marked
/// with `#[parameters]`.
enum FilterStructField<'a> {
    FilterParameters(FilterField<'a>),
    RegularField(FilterField<'a>),
}

impl<'a> FilterStructField<'a> {
    /// Creates a new `FilterStruct` from the given `Field`.
    fn from_field(field: &'a Field) -> Self {
        let Field {
            attrs, ident, ty, ..
        } = field;

        let ident = ident.as_ref();

        if attrs.iter().any(|attr| attr.path.is_ident("parameters")) {
            FilterStructField::FilterParameters(FilterField { ident, ty })
        } else {
            FilterStructField::RegularField(FilterField { ident, ty })
        }
    }

    /// Generates the code that gives the value of this field in the constructor
    /// of the `Filter`.
    fn generate_field_value(&self) -> TokenStream {
        match self {
            FilterStructField::FilterParameters(field) => {
                let FilterField { ident, .. } = field;
                if let Some(ident) = ident {
                    quote! {
                        #ident: parameters,
                    }
                } else {
                    quote! {
                        parameters,
                    }
                }
            }
            FilterStructField::RegularField(field) => {
                let FilterField { ident, ty } = field;
                if let Some(ident) = ident {
                    quote! {
                        #ident: <#ty as ::std::default::Default>::default(),
                    }
                } else {
                    quote! {
                        <#ty as ::std::default::Default>::default(),
                    }
                }
            }
        }
    }

    /// Returns whether this is a field marked with `#[parameters]`
    fn is_filter_parameters(&self) -> bool {
        matches!(self, FilterStructField::FilterParameters(_))
    }
}

/// A field in `FilterStruct`.
struct FilterField<'a> {
    ident: Option<&'a Ident>,
    ty: &'a Type,
}

/// Generates implementation of `From<FilterParameters>`.
fn generate_from_filter_parameters(filter: &FilterStruct<'_>) -> TokenStream {
    let FilterStruct {
        parameters_struct_name,
        fields,
        ty,
        ..
    } = &filter;
    let fields = fields.iter().map(|field| field.generate_field_value());

    let impl_from = filter.generate_impl(quote! { ::std::convert::From<#parameters_struct_name> });

    match ty {
        StructFieldsType::Named => quote! {
            #impl_from {
                fn from(parameters: #parameters_struct_name) -> Self {
                    Self {
                        #(#fields)*
                    }
                }
            }
        },
        StructFieldsType::Unnamed => quote! {
            #impl_from {
                fn from(parameters: #parameters_struct_name) -> Self {
                    Self (
                        #(#fields)*
                    )
                }
            }
        },
        StructFieldsType::Unit => quote! {
            #impl_from {
                fn from(parameters: #parameters_struct_name) -> Self {
                    Self;
                }
            }
        },
    }
}

pub fn derive(input: &DeriveInput) -> TokenStream {
    let filter = match FilterStruct::from_input(input) {
        Ok(filter) => filter,
        Err(err) => return err.to_compile_error(),
    };

    generate_from_filter_parameters(&filter)
}
