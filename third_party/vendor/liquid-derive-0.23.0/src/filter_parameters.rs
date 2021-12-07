use crate::helpers::*;
use proc_macro2::*;
use proc_quote::*;
use std::str::FromStr;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::*;

/// Struct that contains information to generate the necessary code for `FilterParameters`.
struct FilterParameters<'a> {
    name: &'a Ident,
    evaluated_name: Ident,
    fields: FilterParametersFields<'a>,
    vis: &'a Visibility,
}

impl<'a> FilterParameters<'a> {
    /// Searches for `#[evaluated(...)]` in order to parse `evaluated_name`.
    fn parse_attrs(attrs: &[Attribute]) -> Result<Option<Ident>> {
        let mut evaluated_attrs = attrs.iter().filter(|attr| attr.path.is_ident("evaluated"));

        match (evaluated_attrs.next(), evaluated_attrs.next()) {
            (Some(attr), None) => Ok(Self::parse_evaluated_attr(attr)?.get_ident().cloned()),

            (_, Some(attr)) => Err(Error::new_spanned(
                attr,
                "Found multiple definitions for `evaluated` attribute.",
            )),

            _ => Ok(None),
        }
    }

    /// Parses `#[evaluated(...)]` attribute.
    fn parse_evaluated_attr(attr: &Attribute) -> Result<Path> {
        let meta = attr.parse_meta().map_err(|err| {
            Error::new(
                err.span(),
                format!("Could not parse `evaluated` attribute: {}", err),
            )
        })?;

        match meta {
            Meta::Path(meta) => Err(Error::new_spanned(
                meta,
                "Couldn't parse evaluated attribute. Have you tried `#[evaluated(\"...\")]`?",
            )),
            Meta::NameValue(meta) => Err(Error::new_spanned(
                meta,
                "Couldn't parse evaluated attribute. Have you tried `#[evaluated(\"...\")]`?",
            )),
            Meta::List(meta) => {
                let meta_span = meta.span();
                let mut inner = meta.nested.into_iter();

                match (inner.next(), inner.next()) {
                    (Some(inner), None) => {
                        if let NestedMeta::Meta(Meta::Path(ident)) = inner {
                            Ok(ident)
                        } else {
                            Err(Error::new_spanned(inner, "Expected ident."))
                        }
                    }

                    (_, Some(inner)) => Err(Error::new_spanned(inner, "Unexpected element.")),

                    _ => Err(Error::new(meta_span, "Expected ident.")),
                }
            }
        }
    }

    /// Tries to create a new `FilterParameters` from the given `DeriveInput`
    fn from_input(input: &'a DeriveInput) -> Result<Self> {
        let DeriveInput {
            attrs,
            vis,
            generics,
            data,
            ident,
        } = input;

        if !generics.params.is_empty() {
            return Err(Error::new_spanned(
                generics,
                "Generics are cannot be used in FilterParameters.",
            ));
        }

        let fields = match data {
            Data::Struct(data) => FilterParametersFields::from_fields(&data.fields)?,
            Data::Enum(data) => {
                return Err(Error::new_spanned(
                    data.enum_token,
                    "Enums cannot be FilterParameters.",
                ));
            }
            Data::Union(data) => {
                return Err(Error::new_spanned(
                    data.union_token,
                    "Unions cannot be FilterParameters.",
                ));
            }
        };

        if let Some(parameter) = fields.required_after_optional() {
            return Err(Error::new_spanned(
                parameter,
                "Found required positional parameter after an optional positional parameter. The user can't input this parameters without inputing the optional ones first.",
            ));
        }

        let name = ident;
        let evaluated_name = Self::parse_attrs(attrs)?
            .unwrap_or_else(|| Ident::new(&format!("Evaluated{}", name), Span::call_site()));

        Ok(FilterParameters {
            name,
            evaluated_name,
            fields,
            vis,
        })
    }
}

/// Struct that contains `FilterParameter`s.
struct FilterParametersFields<'a> {
    parameters: Punctuated<FilterParameter<'a>, Token![,]>,
}

impl<'a> FilterParametersFields<'a> {
    /// Returns the first required positional parameter (if any) that appears after an optional
    /// positional parameter.
    ///
    /// All optional positional parameters must appear after every required positional parameter.
    /// If this function returns `Some`, the macro is supposed to fail to compile.
    fn required_after_optional(&self) -> Option<&FilterParameter<'_>> {
        self.parameters
            .iter()
            .filter(|parameter| parameter.is_positional())
            .skip_while(|parameter| parameter.is_required())
            .find(|parameter| !parameter.is_optional())
    }

    /// Tries to create a new `FilterParametersFields` from the given `Fields`
    fn from_fields(fields: &'a Fields) -> Result<Self> {
        match fields {
            Fields::Named(fields) => {
                let parameters = fields
                    .named
                    .iter()
                    .map(|field| {
                        let name = field.ident.as_ref().expect("Fields are named.");
                        FilterParameter::new(name, &field)
                    })
                    .collect::<Result<Punctuated<_, Token![,]>>>()?;

                if parameters.is_empty() {
                    Err(Error::new_spanned(
                        fields,
                        "FilterParameters fields must have at least one field. To define an argumentless filter, just skip the `parameters(...)` element in `ParseFilter`.",
                    ))
                } else {
                    Ok(Self { parameters })
                }
            }

            Fields::Unnamed(fields) => {
                Err(Error::new_spanned(
                    fields,
                    "FilterParameters fields must have explicit names. Tuple structs are not allowed.",
                ))
            }

            Fields::Unit => {
                Err(Error::new_spanned(
                    fields,
                    "FilterParameters fields must have at least one field. To define an argumentless filter, just skip the `parameters(...)` element in `ParseFilter`.",
                ))
            }
        }
    }
}

/// Information for a single parameter in a struct that implements `FilterParameters`.
struct FilterParameter<'a> {
    name: &'a Ident,
    is_optional: bool,
    meta: FilterParameterMeta,
}

impl<'a> FilterParameter<'a> {
    /// This message is used a lot in other associated functions
    const ERROR_INVALID_TYPE: &'static str = "Invalid type. All fields in FilterParameters must be either of type `Expression` or `Option<Expression>`";

    /// Helper function for `validate_filter_parameter_fields()`.
    /// Given `::liquid_core::runtime::Expression`, returns `Expression`.
    fn get_type_name(ty: &Type) -> Result<&PathSegment> {
        match ty {
            Type::Path(ty) => {
                let path = match ty.path.segments.last() {
                    Some(path) => path,
                    None => return Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE)),
                };

                Ok(path)
            }
            ty => Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE)),
        }
    }

    /// Returns Some(true) if type is optional, Some(false) if it's not and Err if not a valid type.
    ///
    /// `Expression` => Some(false),
    /// `Option<Expression>` => Some(true),
    ///  _ => Err(...),
    fn parse_type_is_optional(ty: &Type) -> Result<bool> {
        let path = Self::get_type_name(ty)?;
        match path.ident.to_string().as_str() {
            "Option" => match &path.arguments {
                PathArguments::AngleBracketed(arguments) => {
                    let args = &arguments.args;
                    if args.len() != 1 {
                        return Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE));
                    }
                    let arg = match args.last() {
                        Some(arg) => arg,
                        None => return Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE)),
                    };

                    if let GenericArgument::Type(ty) = arg {
                        let path = Self::get_type_name(ty)?;
                        if path.ident.to_string().as_str() == "Expression"
                            && path.arguments.is_empty()
                        {
                            return Ok(true);
                        }
                    }
                    Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE))
                }
                _ => Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE)),
            },
            "Expression" => {
                if !path.arguments.is_empty() {
                    Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE))
                } else {
                    Ok(false)
                }
            }
            _ => Err(Error::new_spanned(ty, Self::ERROR_INVALID_TYPE)),
        }
    }

    /// Creates a new `FilterParameter` from the given `field`, with the given `name`.
    fn new(name: &'a Ident, field: &Field) -> Result<Self> {
        let is_optional = Self::parse_type_is_optional(&field.ty)?;
        let meta = FilterParameterMeta::from_field(&field)?;

        Ok(FilterParameter {
            name,
            is_optional,
            meta,
        })
    }

    /// Returns whether this field is optional.
    fn is_optional(&self) -> bool {
        self.is_optional
    }

    /// Returns whether this field is required (not optional).
    fn is_required(&self) -> bool {
        !self.is_optional
    }

    /// Returns whether this is a positional field.
    fn is_positional(&self) -> bool {
        self.meta.mode == FilterParameterMode::Positional
    }

    /// Returns whether this is a keyword field.
    fn is_keyword(&self) -> bool {
        self.meta.mode == FilterParameterMode::Keyword
    }

    /// Returns the name of this parameter in liquid.
    ///
    /// That is, by default, the name of the field as a string. However,
    /// this name may be overridden by `rename` attribute.
    fn liquid_name(&self) -> String {
        match &self.meta.rename {
            Some(name) => name.clone(),
            None => self.name.to_string(),
        }
    }
}

impl<'a> ToTokens for FilterParameter<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.name.to_tokens(tokens);
    }
}

/// Whether `FilterParameter` is `Keyword` or `Positional`.
#[derive(PartialEq)]
enum FilterParameterMode {
    Keyword,
    Positional,
}

impl FromStr for FilterParameterMode {
    type Err = String;
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "keyword" => Ok(FilterParameterMode::Keyword),
            "positional" => Ok(FilterParameterMode::Positional),
            s => Err(format!(
                "Expected either \"keyword\" or \"positional\". Found \"{}\".",
                s
            )),
        }
    }
}

/// The type that this `FilterParameter` will evaluate to.
enum FilterParameterType {
    // Any value, the default type
    Value,

    // Scalars
    Scalar,
    Integer,
    Float,
    Bool,
    DateTime,
    Date,
    Str,
}

impl FromStr for FilterParameterType {
    type Err = String;
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "any" => Ok(FilterParameterType::Value),
            "scalar" => Ok(FilterParameterType::Scalar),
            "integer" => Ok(FilterParameterType::Integer),
            "float" => Ok(FilterParameterType::Float),
            "bool" => Ok(FilterParameterType::Bool),
            "date_time" => Ok(FilterParameterType::DateTime),
            "date" => Ok(FilterParameterType::Date),
            "str" => Ok(FilterParameterType::Str),
            _ => Err(format!("Expected one of the following: \"any\", \"integer\", \"float\", \"bool\", \"date_time\", \"date\", \"scalar\", or \"str\". Found \"{}\".", s)),
        }
    }
}

/// Struct that contains the information about `FilterParameter` parsed in `#[parameter(...)]` attribute.
struct FilterParameterMeta {
    rename: Option<String>,
    description: String,
    mode: FilterParameterMode,
    ty: FilterParameterType,
}

impl FilterParameterMeta {
    /// Tries to create a new `FilterParameterMeta` from the given `Attribute`
    fn parse_parameter_attribute(attr: &Attribute) -> Result<Self> {
        let meta = attr.parse_meta().map_err(|err| {
            Error::new(
                err.span(),
                format!("Could not parse `parameter` attribute: {}", err),
            )
        })?;

        let meta = match meta {
            Meta::Path(meta) => return Err(Error::new_spanned(
                meta,
                "Found parameter without description. Description is necessary in order to properly generate ParameterReflection.",
            )),
            Meta::NameValue(meta) => return Err(Error::new_spanned(
                meta,
                "Couldn't parse this parameter attribute. Have you tried `#[parameter(description=\"...\")]`?",
            )),
            Meta::List(meta) => meta
        };

        let mut rename = AssignOnce::Unset;
        let mut description = AssignOnce::Unset;
        let mut mode = AssignOnce::Unset;
        let mut ty = AssignOnce::Unset;

        for meta in meta.nested.into_iter() {
            if let NestedMeta::Meta(Meta::NameValue(meta)) = meta {
                let key = &meta.path.get_ident().expect("Single element path");
                let value = &meta.lit;

                match key.to_string().as_str() {
                    "rename" => assign_str_value(&mut rename, key, value)?,
                    "description" => assign_str_value(&mut description, key, value)?,
                    "mode" => parse_str_value(&mut mode, key, value)?,
                    "arg_type" => parse_str_value(&mut ty, key, value)?,
                    _ => {
                        return Err(Error::new_spanned(
                            key,
                            "Unknown element in parameter attribute.",
                        ));
                    }
                }
            } else {
                return Err(Error::new_spanned(
                    meta,
                    "Unknown element in parameter attribute. All elements should be key=value pairs.",
                ));
            }
        }

        let rename = rename.into_option();
        let description = description.unwrap_or_err(|| Error::new_spanned(
            attr,
            "Found parameter without description. Description is necessary in order to properly generate ParameterReflection.",
        ))?;
        let mode = mode.default_to(FilterParameterMode::Positional);
        let ty = ty.default_to(FilterParameterType::Value);

        Ok(FilterParameterMeta {
            rename,
            description,
            mode,
            ty,
        })
    }

    /// Tries to create a new `FilterParameterMeta` from the given field.
    fn from_field(field: &Field) -> Result<Self> {
        let mut parameter_attrs = field
            .attrs
            .iter()
            .filter(|attr| attr.path.is_ident("parameter"));

        match (parameter_attrs.next(), parameter_attrs.next()) {
            (Some(attr), None) => Self::parse_parameter_attribute(attr),

            (_, Some(attr)) => Err(Error::new_spanned(
                attr,
                "Found multiple definitions for `parameter` attribute.",
            )),

            _ => Err(Error::new_spanned(
                field,
                "Found parameter without #[parameter] attribute. All filter parameters must be accompanied by this attribute.",
            )),
        }
    }
}

/// Generates the statement that assigns the next positional argument.
fn generate_construct_positional_field(
    field: &FilterParameter<'_>,
    required: usize,
) -> TokenStream {
    let name = &field.name;

    if field.is_optional() {
        quote! {
            let #name = args.positional.next();
        }
    } else {
        let plural = if required == 1 { None } else { Some("s") };
        quote! {
            let #name = args.positional.next().ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid number of arguments")
                    .context("cause", concat!("expected at least ", #required, " positional argument", #plural))
            )?;
        }
    }
}

/// Generates the statement that evaluates the `Expression`
fn generate_evaluate_field(field: &FilterParameter<'_>) -> TokenStream {
    let name = &field.name;
    let liquid_name = field.liquid_name();
    let ty = &field.meta.ty;

    let to_type = match ty {
        FilterParameterType::Value => quote! { ::std::result::Result::Ok(#name) },
        FilterParameterType::Scalar => quote! {
            match #name {
                ::liquid_core::ValueCow::Owned(v) => {
                    v.as_scalar().into_owned()
                },
                ::liquid_core::ValueCow::Borrowed(v) => {
                    v.as_scalar()
                },
            }.ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid argument")
                    .context("argument", #liquid_name)
                    .context("cause", "Scalar expected")
            )
        },
        FilterParameterType::Integer => quote! {
            #name.as_scalar()
            .and_then(|s| s.to_integer())
            .ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid argument")
                    .context("argument", #liquid_name)
                    .context("cause", "Whole number expected")
            )
        },
        FilterParameterType::Float => quote! {
            #name.as_scalar()
            .and_then(|s| s.to_float())
            .ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid argument")
                    .context("argument", #liquid_name)
                    .context("cause", "Fractional number expected")
            )
        },
        FilterParameterType::Bool => quote! {
            #name.as_scalar()
            .and_then(|s| s.to_bool())
            .ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid argument")
                    .context("argument", #liquid_name)
                    .context("cause", "Boolean expected")
            )
        },
        FilterParameterType::DateTime => quote! {
            #name.as_scalar()
            .and_then(|s| s.to_date_time())
            .ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid argument")
                    .context("argument", #liquid_name)
                    .context("cause", "DateTime expected")
            )
        },
        FilterParameterType::Date => quote! {
            #name.as_scalar()
            .and_then(|s| s.to_date())
            .ok_or_else(||
                ::liquid_core::error::Error::with_msg("Invalid argument")
                    .context("argument", #liquid_name)
                    .context("cause", "Date expected")
            )
        },
        FilterParameterType::Str => quote! {
            match #name {
                ::liquid_core::ValueCow::Owned(v) => {
                    ::std::result::Result::Ok(v.to_kstr().into_owned().into())
                },
                ::liquid_core::ValueCow::Borrowed(v) => {
                    ::std::result::Result::Ok(v.to_kstr())
                },
            }
        },
    };

    if field.is_optional() {
        quote! {
            let #name = self.#name.as_ref().map(|field| {
                let #name = field.evaluate(runtime)?;
                let #name = #to_type?;
                ::std::result::Result::Ok(#name)
            }).transpose()?;
        }
    } else {
        quote! {
            let #name = self.#name.evaluate(runtime)?;
            let #name = #to_type?;
        }
    }
}

/// Generates the match arm that assigns the given keyword argument.
fn generate_keyword_match_arm(field: &FilterParameter<'_>) -> TokenStream {
    let rust_name = &field.name;
    let liquid_name = field.liquid_name();

    quote! {
        #liquid_name => if #rust_name.is_none() {
            #rust_name = ::std::option::Option::Some(arg.1);
        } else {
            return ::std::result::Result::Err(::liquid_core::error::Error::with_msg(concat!("Multiple definitions of `", #liquid_name, "`")));
        },
    }
}

/// Generates implementation of `FilterParameters`.
fn generate_impl_filter_parameters(filter_parameters: &FilterParameters<'_>) -> TokenStream {
    let FilterParameters {
        name,
        evaluated_name,
        fields,
        ..
    } = filter_parameters;

    let num_min_positional = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_positional() && parameter.is_required())
        .count();

    let num_max_positional = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_positional())
        .count();

    let too_many_args = {
        let plural = if num_max_positional == 1 {
            None
        } else {
            Some("s")
        };
        quote! {
            ::liquid_core::error::Error::with_msg("Invalid number of positional arguments")
                .context("cause", concat!("expected at most ", #num_max_positional, " positional argument", #plural))
        }
    };

    let field_names = fields.parameters.iter().map(|field| &field.name);
    let comma_separated_field_names = quote! { #(#field_names,)* };

    let evaluate_fields = fields
        .parameters
        .iter()
        .map(|field| generate_evaluate_field(&field));

    let construct_positional_fields = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_positional())
        .map(|field| generate_construct_positional_field(&field, num_min_positional));

    let keyword_fields = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_keyword());

    let match_keyword_parameters_arms = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_keyword())
        .map(|field| generate_keyword_match_arm(&field));

    let unwrap_required_keyword_fields = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_keyword() && parameter.is_required())
        .map(|field| {
            let liquid_name = field.liquid_name();
            quote!{ let #field = #field.ok_or_else(|| ::liquid_core::error::Error::with_msg(concat!("Expected named argument `", #liquid_name, "`")))?; }
        });

    quote! {
        impl<'a> ::liquid_core::parser::FilterParameters<'a> for #name {
            type EvaluatedFilterParameters = #evaluated_name<'a>;

            fn from_args(mut args: ::liquid_core::parser::FilterArguments) -> ::liquid_core::error::Result<Self> {
                #(#construct_positional_fields)*
                if let ::std::option::Option::Some(arg) = args.positional.next() {
                    return ::std::result::Result::Err(#too_many_args);
                }

                #(let mut #keyword_fields = ::std::option::Option::None;)*
                #[allow(clippy::never_loop)] // This is not obfuscating the code because it's generated by a macro
                while let ::std::option::Option::Some(arg) = args.keyword.next() {
                    match arg.0 {
                        #(#match_keyword_parameters_arms)*
                        keyword => return ::std::result::Result::Err(::liquid_core::error::Error::with_msg(format!("Unexpected named argument `{}`", keyword))),
                    }
                }
                #(#unwrap_required_keyword_fields)*

                Ok( #name { #comma_separated_field_names } )
            }

            fn evaluate(&'a self, runtime: &'a dyn ::liquid_core::runtime::Runtime) -> ::liquid_core::error::Result<Self::EvaluatedFilterParameters> {
               #(#evaluate_fields)*

                Ok( #evaluated_name { #comma_separated_field_names __phantom_data: ::std::marker::PhantomData } )
            }
        }
    }
}

/// Generates `EvaluatedFilterParameters` struct.
fn generate_evaluated_struct(filter_parameters: &FilterParameters<'_>) -> TokenStream {
    let FilterParameters {
        evaluated_name,
        fields,
        vis,
        ..
    } = filter_parameters;

    let field_types = fields.parameters.iter().map(|field| {
        let ty = match &field.meta.ty {
            FilterParameterType::Value => quote! { ::liquid_core::model::ValueCow<'a> },
            FilterParameterType::Scalar => quote! { ::liquid_core::model::ScalarCow<'a> },
            FilterParameterType::Integer => quote! { i64 },
            FilterParameterType::Float => quote! { f64 },
            FilterParameterType::Bool => quote! { bool },
            FilterParameterType::DateTime => quote! { ::liquid_core::model::DateTime },
            FilterParameterType::Date => quote! { ::liquid_core::model::Date },
            FilterParameterType::Str => quote! { ::kstring::KStringCow<'a> },
        };

        if field.is_optional() {
            quote! { ::std::option::Option< #ty > }
        } else {
            quote! { #ty }
        }
    });

    let field_names = fields.parameters.iter().map(|field| &field.name);

    quote! {
        #vis struct #evaluated_name <'a>{
            #(#field_names : #field_types,)*
            __phantom_data: ::std::marker::PhantomData<&'a ()>
        }
    }
}

/// Constructs `ParameterReflection` for the given parameter.
fn generate_parameter_reflection(field: &FilterParameter<'_>) -> TokenStream {
    let name = field.liquid_name();
    let description = &field.meta.description.to_string();
    let is_optional = field.is_optional();

    quote! {
        ::liquid_core::parser::ParameterReflection {
            name: #name,
            description: #description,
            is_optional: #is_optional,
        },
    }
}

/// Generates implementation of `FilterParametersReflection`.
fn generate_impl_reflection(filter_parameters: &FilterParameters<'_>) -> TokenStream {
    let FilterParameters { name, fields, .. } = filter_parameters;

    let kw_params_reflection = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_keyword())
        .map(generate_parameter_reflection);

    let pos_params_reflection = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_positional())
        .map(generate_parameter_reflection);

    quote! {
        impl ::liquid_core::parser::FilterParametersReflection for #name {
            fn positional_parameters() -> &'static [::liquid_core::parser::ParameterReflection] {
                &[ #(#pos_params_reflection)* ]
            }

            fn keyword_parameters() -> &'static [::liquid_core::parser::ParameterReflection] {
                &[ #(#kw_params_reflection)* ]
            }
        }
    }
}

/// Helper function for `generate_impl_display`
fn generate_access_positional_field_for_display(field: &FilterParameter<'_>) -> TokenStream {
    let rust_name = &field.name;

    if field.is_optional() {
        quote! {
            self.#rust_name.as_ref()
        }
    } else {
        quote! {
            ::std::option::Option::Some(&self.#rust_name)
        }
    }
}

/// Helper function for `generate_impl_display`
fn generate_access_keyword_field_for_display(field: &FilterParameter<'_>) -> TokenStream {
    let rust_name = &field.name;
    let liquid_name = field.liquid_name();

    if field.is_optional() {
        quote! {
            (#liquid_name, self.#rust_name.as_ref())
        }
    } else {
        quote! {
            (#liquid_name, ::std::option::Option::Some(&self.#rust_name))
        }
    }
}

/// Generates implementation of `Display`.
fn generate_impl_display(filter_parameters: &FilterParameters<'_>) -> TokenStream {
    let FilterParameters { name, fields, .. } = filter_parameters;

    let positional_fields = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_positional())
        .map(|field| generate_access_positional_field_for_display(&field));

    let keyword_fields = fields
        .parameters
        .iter()
        .filter(|parameter| parameter.is_keyword())
        .map(|field| generate_access_keyword_field_for_display(&field));

    quote! {
        impl ::std::fmt::Display for #name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                let positional = [#(#positional_fields ,)*];
                let keyword = [#(#keyword_fields ,)*];

                let positional = positional
                    .iter()
                    .filter_map(|p: &::std::option::Option<&::liquid_core::runtime::Expression>| p.as_ref())
                    .map(|p| p.to_string());
                let keyword = keyword.iter().filter_map(|p: &(&str, ::std::option::Option<&::liquid_core::runtime::Expression>)| match p.1 {
                    ::std::option::Option::Some(p1) => ::std::option::Option::Some(format!("{}: {}", p.0, p1)),
                    ::std::option::Option::None => ::std::option::Option::None,
                });

                let parameters = positional
                    .chain(keyword)
                    .collect::<::std::vec::Vec<::std::string::String>>()
                    .join(", ");

                write!(
                    f,
                    "{}",
                    parameters
                )
            }
        }
    }
}

pub fn derive(input: &DeriveInput) -> TokenStream {
    let filter_parameters = match FilterParameters::from_input(input) {
        Ok(filter_parameters) => filter_parameters,
        Err(err) => return err.to_compile_error(),
    };

    let mut output = TokenStream::new();
    output.extend(generate_impl_filter_parameters(&filter_parameters));
    output.extend(generate_impl_reflection(&filter_parameters));
    output.extend(generate_impl_display(&filter_parameters));
    output.extend(generate_evaluated_struct(&filter_parameters));

    output
}
