use std::fmt::{Debug, Display};

use crate::error::Result;
use crate::model::{Value, ValueView};
use crate::runtime::{Expression, Runtime};

/// A structure that holds the information of a single parameter in a filter.
/// This includes its name, description and whether it is optional or required.
///
/// This is the return type in some `FilterReflection` functions.
pub struct ParameterReflection {
    pub name: &'static str,
    pub description: &'static str,
    pub is_optional: bool,
}

/// A trait that holds the information of the parameters of a filter.
///
/// All structs that implement `FilterParameters` must implement this.
/// This is actually automatically implemented with `#[derive(FilterParameters)]`.
///
/// This trait allows `FilterReflection` macro to extract the parameters information
/// from a given `FilterParameters` structure.
pub trait FilterParametersReflection {
    fn positional_parameters() -> &'static [ParameterReflection];
    fn keyword_parameters() -> &'static [ParameterReflection];
}

/// A trait that holds the information of a filter about itself, such as
/// its name, description and parameters.
///
/// All structs that implement `ParseFilter` must implement this.
///
/// # Deriving
///
/// This trait may be derived with `liquid-derive`'s `#[derive(FilterReflection)]`. However,
/// it is necessary to use the `#[filter(...)]`  helper attribute. See documentation on
/// `liquid-derive` for more information.
pub trait FilterReflection {
    fn name(&self) -> &str;
    fn description(&self) -> &str;

    fn positional_parameters(&self) -> &'static [ParameterReflection];
    fn keyword_parameters(&self) -> &'static [ParameterReflection];
}

/// A trait that declares and holds the parameters of a filter.
///
/// Provides `from_args`, to construct itself from `FilterArguments` (parses the arguments)
/// and `evaluate`, to construct its evaluated counterpart (evaluates the arguments).
///
/// # Deriving
///
/// The whole point of this structure is to facilitate the process of deriving a filter.
/// Thus, this trait and all traits it requires may be derived with `#[derive(Debug, FilterParameters)]`.
///
/// See documentation for `FilterParameters` macro on `liquid-derive` for more information.
pub trait FilterParameters<'a>: Sized + FilterParametersReflection + Debug + Display {
    type EvaluatedFilterParameters;
    fn from_args(args: FilterArguments) -> Result<Self>;
    fn evaluate(&'a self, runtime: &'a dyn Runtime) -> Result<Self::EvaluatedFilterParameters>;
}

/// Structure that holds the unparsed arguments of a filter, both positional and keyword.
pub struct FilterArguments<'a> {
    pub positional: Box<dyn Iterator<Item = Expression>>,
    pub keyword: Box<dyn Iterator<Item = (&'a str, Expression)> + 'a>,
}

/// A trait that holds a filter, ready to evaluate.
///
/// # Deriving
///
/// You cannot derive `Filter`, as it would go against the very point of creating your own filter.
/// You can, however, derive some other traits that are necessary in order to implement it.
///
/// In order to implement this trait, the struct must also implement `Debug` and `Display`, as well
/// as either `Default` or `From<T>` (where T is the FilterParameters struct), respectively, in a
/// filter without or with parameters.
///
/// For `Debug` and `Default`, one may use rust's `#[derive(Debug)]` and `#[derive(Default)]` macros.
/// For `Display` and `From<T>`, one may use `liquid-derive`'s `#[derive(Display_filter)]` and
/// `#[derive(FromFilterParameters)]`.
///
/// Note, however, that you may need helper attributes like `#[name = "..."]` and `#[parameters]` for
/// using liquid-derive`'s macros. See documentation on `liquid-derive` for more information.
///
/// # Examples
///
/// Filter for filter with no arguments:
/// ```ignore
/// #[derive(Debug, Default, Display_filter)]
/// #[name = "abs"] // The name of the filter, for `Display_filter`.
/// struct AbsFilter; // There are no parameters, so implements `Default`.
///
/// impl Filter for AbsFilter {
///     fn evaluate(&self, input: &dyn  ValueView, _runtime: &dyn Runtime) -> Result<Value> {
///         // Implementation of the filter here
///     }
/// }
/// ```
///
/// Filter for filter with arguments:
/// ```ignore
/// #[derive(Debug, FromFilterParameters, Display_filter)]
/// #[name = "at_least"] // The name of the filter for derives
/// struct AtLeastFilter { // There are parameters, so derives `FromFilterParameters`.
///     #[parameters] // Mark the FilterParameters struct for derives
///     args: AtLeastArgs, // A struct that implements `FilterParameters`
/// }
///
/// impl Filter for AtLeastFilter {
///     fn evaluate(&self, input: &ValueViwe, runtime: &dyn Runtime) -> Result<Value> {
///         // Evaluate the `FilterParameters`
///         let args = self.args.evaluate(runtime)?;
///
///         // Implementation of the filter here
///     }
/// }
/// ```
///
/// Filter for a configurable filter:
/// ```ignore
/// #[derive(Debug, Display_filter)]
/// #[name = "example"] // The name of the filter for `Display`
/// // Because construction happens manually (without derive) in `FilterParser`
/// // no need to derive neither `Default` nor `FromFilterParameters`.
/// struct ExampleFilter {
///     #[parameters] // Mark the FilterParameters struct for `Display`
///     args: ExampleArgs, // A struct that implements `FilterParameters`
///     state: i32, // See `ParseFilter` example for runtime
/// }
///
/// impl Filter for AtLeastFilter {
///     fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
///         // Evaluate the `FilterParameters`
///         let args = self.args.evaluate(runtime)?;
///
///         // Implementation of the filter here
///     }
/// }
/// ```
pub trait Filter: Send + Sync + Debug + Display {
    // This will evaluate the expressions and evaluate the filter.
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value>;
}

/// A trait to register a new filter in the `liquid::Parser`.
///
/// To implement this trait, the structure must also implement `FilterReflection`, thus giving
/// meta information about the filter (namely it's name).
///
/// Every time a filter with that name is encountered, it is parsed with the `ParseFilter::parse`
/// method, yielding a new `Filter`.
///
/// # Deriving
///
/// In order to implement this trait, the struct must also implement `FilterReflection` and
/// `Clone`.
///
/// `Clone` may be derived with rust's `#[derive(Clone)]`. `FilterReflection` may be derived
/// with `liquid-derive`'s `#[derive(FilterReflection)]`. ParseFilter may be derived with
/// `#[derive(FilterReflection)]`.
///
/// In order to use `liquid-derive`'s macros, however, it is necessary to use the `#[filter(...)]`
/// helper attribute. See documentation on `liquid-derive` for more information.
///
/// # Examples
///
/// ParseFilter for filter with no arguments:
/// ```ignore
/// #[derive(Clone, ParseFilter, FilterReflection)]
/// #[filter(
///     name = "abs",
///     description = "Returns the absolute value of a number.",
///     parsed(AbsFilter) // A struct that implements `Filter` (must implement `Default`)
/// )]
/// pub struct Abs;
/// ```
///
/// ParseFilter for filter with arguments:
/// ```ignore
/// #[derive(Clone, ParseFilter, FilterReflection)]
/// #[filter(
///     name = "slice",
///     description = "Takes a slice of a given string or array.",
///     parameters(SliceArgs), // A struct that implements `FilterParameters`
///     parsed(SliceFilter) // A struct that implements `Filter` (must implement `From<SliceArgs>`)
/// )]
/// pub struct Slice;
/// ```
///
/// ParseFilter for a configurable filter:
/// ```ignore
/// #[derive(Clone, FilterReflection)]
/// #[filter(
///     name = "example",
///     description = "This filter exists for example purposes.",
///     parameters(ExampleArgs) // A struct that implements `FilterParameters`
/// )]
/// pub struct ExampleParser {
///     // You can add as many fields as you find necessary to configure the filter
///     // before registering it.
///     pub mode: i32,
/// }
///
/// // For configurable filters, there is no default implementation of `ParseFilter`
/// impl ParseFilter for ExampleParser {
///     fn parse(&self, arguments: FilterArguments) -> Result<Box<Filter>> {
///         // Create the `FilterParameters` struct from the given `arguments`
///         let args = ExampleArgs::from_args(arguments)?;
///         // Use the configuration state of the `ParseFilter`
///         let state = self.state;
///
///         // Create the `Filter` struct and return it, passing the information
///         // about the arguments and the configuration of the `ParseFilter`.
///         Ok(Box::new(ExampleFilter { args, state }))
///     }
/// }
/// ```
pub trait ParseFilter: Send + Sync + ParseFilterClone {
    /// Filter `input` based on `arguments`.
    fn parse(&self, arguments: FilterArguments) -> Result<Box<dyn Filter>>;

    fn reflection(&self) -> &dyn FilterReflection;
}

/// Support cloning of `Box<ParseFilter>`.
pub trait ParseFilterClone {
    /// Cloning of `dyn ParseFilter`.
    fn clone_box(&self) -> Box<dyn ParseFilter>;
}

impl<T> ParseFilterClone for T
where
    T: 'static + ParseFilter + Clone,
{
    fn clone_box(&self) -> Box<dyn ParseFilter> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn ParseFilter> {
    fn clone(&self) -> Box<dyn ParseFilter> {
        self.clone_box()
    }
}

impl<T> From<T> for Box<dyn ParseFilter>
where
    T: 'static + ParseFilter,
{
    fn from(filter: T) -> Self {
        Box::new(filter)
    }
}
