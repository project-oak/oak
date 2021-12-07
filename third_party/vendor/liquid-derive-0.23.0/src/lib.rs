//! Derive macros to aid in filter creation.

extern crate proc_macro;

mod filter;
mod filter_parameters;
pub(crate) mod helpers;
mod object_view;
mod parse_filter;
mod value_view;

use proc_macro::TokenStream;

/// Implements `FilterParameters`, as well as two of the traits it requires
/// (`Display` and `FilterParametersReflection`) and its evaluated counterpart.
///
/// Before declaring the struct, the `#[evaluated = "..."]` attribute may be
/// used to rename the evaluated counterpart (defaults to this struct's name
/// prepended by "Evaluated"). This may be useful to avoid name collisions.
///
/// Each parameter has the following structure:
/// ```ignore
/// #[parameter(...)]
/// NAME: TYPE
/// ```
///
/// `NAME` will be the name of the parameter (although it may be renamed
/// if it collides with a rust keyword, see below for more information).
///
/// `TYPE` will be either `Expression` or `Option<Expression>`, marking the
/// parameter, respectively, as either required or optional. Note `Expression`
/// here is the type `::liquid_core::runtime::Expression`.
///
/// Inside the `#[parameter(...)]` attribute there may be some information
/// about the parameter, such as:
///     - `description` -> (REQUIRED) the description of this parameter for
/// `FilterReflection`
///     - `rename` -> overrides `NAME` as the liquid name of the parameter
/// (to avoid collisions with rust keywords)
///     - `mode` -> either "keyword" or "positional" (defaults to "positional")
///     - `arg_type` -> a shortcut to unwrap the content of a value while evaluating
/// the argument (defaults to "any"). See below for more information.
///
/// # Argument Type
///
/// If you want to only accept a certain type of `Value` for a given argument,
/// you may mark its type with `arg_type = "..."`. This will take away the burden
/// and boilerplate of handling errors and unwraping the liquid `Value` into a rust
/// type.
///
/// Right now, there is a default `arg_type`, "any", that accepts any value, as well
/// as other 6 types, one for each type of `Scalar`:
///     - "any" -> any `Value` is accepted, this is the default option and `evaluate` will
/// only convert `Expression` to `Value`.
///     - "integer" -> only `Scalar(Integer)` is accepted, `evaluate` will unwrap `Value`
/// into `i64`.
///     - "float" -> only `Scalar(Float)` is accepted, `evaluate` will unwrap `Value`
/// into `f64`.
///     - "bool" -> only `Scalar(Bool)` is accepted, `evaluate` will unwrap `Value`
/// into `bool`.
///     - "date" -> only `Scalar(Date)` is accepted, `evaluate` will unwrap `Value`
/// into `Date`.
///     - "str" -> only `Scalar(Str)` is accepted, `evaluate` will unwrap `Value`
/// into `KStringCow`.
///
/// # Examples
///
/// From slice filter:
/// ```ignore
/// #[derive(Debug, FilterParameters)]
/// struct SliceArgs {
///     #[parameter(
///         description = "The offset of the slice.",
///         arg_type = "integer" // Only integer scalars are accepted
///     )]
///     offset: Expression, // Required parameter named `offset`
///
///     #[parameter(
///         description = "The length of the slice.",
///         arg_type = "integer" // Only integer scalars are accepted
///     )]
///     length: Option<Expression>, // Optional parameter named `length`
/// }
/// ```
///
/// From test filter:
/// ```ignore
/// #[derive(Debug, FilterParameters)]
/// // The evaluated counterpart of this `FilterParameters` would have been
/// // `EvaluatedTestMixedFilterParameters`, but because of this attribute
/// // it will be named `TestMixedFilterParametersEvaluated` instead.
/// #[evaluated(TestMixedFilterParametersEvaluated)]
/// struct TestMixedFilterParameters {
///     #[parameter(
///         description = "1",
///         arg_type = "integer", // Only integer scalars are accepted
///         mode = "keyword" // This is a keyword parameter
///     )]
///     a: Option<Expression>, // Optional parameter named `a`
///
///     #[parameter(
///         description = "2",
///         arg_type = "bool" // Only boolean scalars are accepted
///     )]
///     b: Expression, // Required parameter named `b`
///
///     #[parameter(
///         description = "3",
///         arg_type = "float", // Only floating point scalars are accepted
///         mode = "keyword" // This is a keyword parameter
///     )]
///     c: Option<Expression>, // Optional parameter named `c`
///
///     #[parameter(
///         description = "4",
///         arg_type = "date" // Only date scalars are accepted
///     )]
///     d: Expression, // Required parameter named `d`
///
///     #[parameter(
///         description = "5",
///         arg_type = "str" // Only string scalars are accepted
///     )]
///     e: Option<Expression>, // Optional parameter named `e`
///
///     #[parameter(
///         rename = "type", // Will override field name in liquid
///         description = "6",
///         arg_type = "any", // Any `Value` is accepted. This is the same as not defining `arg_type`
///         mode = "keyword" // This is a keyword parameter
///     )]
///     f: Expression, // Required parameter named `type` (see `rename` in attribute)
/// }
/// ```
#[proc_macro_derive(FilterParameters, attributes(parameter, evaluated))]
pub fn derive_filter_parameters(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    filter_parameters::derive(&input).into()
}

/// Implements `ParseFilter`.
///
/// This is only useful for stateless filters (the most common case). For
/// filters with configurable state, you will need to implement this trait
/// manually.
///
/// Requires the `#[filter(...)]` attribute to define the filter, with the
/// following information:
///     - `parameters` -> (OPTIONAL) only required if the filter has parameters,
/// the `FilterParameters` struct
///     - `parsed` -> the `Filter` struct
///
/// # Example
///
/// ```ignore
/// #[derive(Clone, ParseFilter, FilterReflection)]
/// #[filter(
///     name = "slice",  // Required by `FilterReflection`, not `ParseFilter`
///     description = "Takes a slice of a given string or array.", // Required by `FilterReflection`, not `ParseFilter`
///     parameters(SliceArgs), // The filter has parameters
///     parsed(SliceFilter)
/// )]
/// pub struct Slice;
/// ```
#[proc_macro_derive(ParseFilter, attributes(filter))]
pub fn derive_parse_filter(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    parse_filter::parse::derive(&input).into()
}

/// Implements `FilterReflection` for a structure that intends to implement
/// the `ParseFilter` trait.
///
/// Requires the `#[filter(...)]` attribute to define the filter, with the
/// following information:
///     - `name` -> the name of the filter
///     - `description` -> the description of the filter
///     - `parameters` -> (OPTIONAL) only required if the filter has parameters,
/// the `FilterParameters` struct
///
/// # Example
///
/// ```ignore
/// #[derive(Clone, ParseFilter, FilterReflection)]
/// #[filter(
///     name = "slice",
///     description = "Takes a slice of a given string or array.",
///     parameters(SliceArgs), // The filter has parameters
///     parsed(SliceFilter) // Required by `ParseFilter`, not `FilterReflection`
/// )]
/// pub struct Slice;
/// ```
#[proc_macro_derive(FilterReflection, attributes(filter))]
pub fn derive_filter_reflection(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    parse_filter::filter_reflection::derive(&input).into()
}

/// Implements `From<T>` (T implements FilterParameters) for a structure that
/// intends to implement the `Filter` trait.
///
/// The field that holds the parameters must be marked with `#[parameters]`.
///
/// # Example
///
/// ```ignore
/// #[derive(Debug, FromFilterParameters, Display_filter)]
/// #[name = "at_least"]
/// struct AtLeastFilter {
///     #[parameters] // Mark the FilterParameters struct
///     args: AtLeastArgs, // A struct that implements `FilterParameters`
/// }
///
/// impl Filter for AtLeastFilter {
///     // ...
/// }
/// ```
#[proc_macro_derive(FromFilterParameters, attributes(parameters))]
pub fn derive_from_filter_parameters(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    filter::from_filter_parameters::derive(&input).into()
}

/// Implements `Display` for a structure that intends to implement the `Filter`
/// trait.
///
/// Requires the helper attribute `#[name = "..."]` to tell the name of the
/// filter before its declaration.
///
/// If the filter has parameters, the field that holds them must be marked
/// with `#[parameters]`.
///
/// # Example
///
/// ```ignore
/// #[derive(Debug, FromFilterParameters, Display_filter)]
/// #[name = "at_least"] // The name of the filter
/// struct AtLeastFilter {
///     #[parameters] // Mark the FilterParameters struct
///     args: AtLeastArgs, // A struct that implements `FilterParameters`
/// }
///
/// impl Filter for AtLeastFilter {
///     // ...
/// }
/// ```
#[proc_macro_derive(Display_filter, attributes(name, parameters))]
pub fn derive_display_filter(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    filter::display::derive(&input).into()
}

#[proc_macro_derive(CoreValueView)]
pub fn derive_core_value_view(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    value_view::core_derive(&input).into()
}

#[proc_macro_derive(CoreObjectView)]
pub fn derive_core_object_view(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    object_view::core_derive(&input).into()
}

#[proc_macro_derive(ValueView)]
pub fn derive_value_view(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    value_view::derive(&input).into()
}

#[proc_macro_derive(ObjectView)]
pub fn derive_object_view(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::DeriveInput);
    object_view::derive(&input).into()
}
