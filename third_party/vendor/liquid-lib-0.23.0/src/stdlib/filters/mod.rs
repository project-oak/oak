use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

mod array;
mod date;
mod html;
mod math;
mod slice;
mod string;
mod url;

pub use self::array::{
    Compact, Concat, First, Join, Last, Map, Reverse, Sort, SortNatural, Uniq, Where,
};
pub use self::date::Date;
pub use self::html::{Escape, EscapeOnce, NewlineToBr, StripHtml};
pub use self::math::{
    Abs, AtLeast, AtMost, Ceil, DividedBy, Floor, Minus, Modulo, Plus, Round, Times,
};
pub use self::slice::Slice;
pub use self::string::case::{Capitalize, Downcase, Upcase};
pub use self::string::operate::{Append, Prepend, Remove, RemoveFirst, Replace, ReplaceFirst};
pub use self::string::strip::{Lstrip, Rstrip, Strip, StripNewlines};
pub use self::string::truncate::{Truncate, TruncateWords};
pub use self::string::Split;
pub use self::url::{UrlDecode, UrlEncode};

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "size",
    description = "Returns the size of the input. For an array or object this is the number of elements. For other values it's the length of its string representation.",
    parsed(SizeFilter)
)]
pub struct Size;

#[derive(Debug, Default, Display_filter)]
#[name = "size"]
struct SizeFilter;

impl Filter for SizeFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        if let Some(x) = input.as_scalar() {
            Ok(Value::scalar(x.to_kstr().len() as i64))
        } else if let Some(x) = input.as_array() {
            Ok(Value::scalar(x.size()))
        } else if let Some(x) = input.as_object() {
            Ok(Value::scalar(x.size()))
        } else {
            Ok(Value::scalar(0i64))
        }
    }
}

#[derive(Debug, FilterParameters)]
struct DefaultArgs {
    #[parameter(description = "The default value.")]
    default: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "default",
    description = "Sets a default value for the given input.",
    parameters(DefaultArgs),
    parsed(DefaultFilter)
)]
pub struct Default;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "default"]
struct DefaultFilter {
    #[parameters]
    args: DefaultArgs,
}

impl Filter for DefaultFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        if input.query_state(liquid_core::model::State::DefaultValue) {
            Ok(args.default.to_value())
        } else {
            Ok(input.to_value())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use liquid_core::Object;

    #[test]
    fn unit_size() {
        assert_eq!(
            liquid_core::call_filter!(Size, "abc").unwrap(),
            Value::scalar(3f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Size, "this has 22 characters").unwrap(),
            Value::scalar(22f64)
        );
        assert_eq!(
            liquid_core::call_filter!(
                Size,
                Value::Array(vec![
                    Value::scalar(0f64),
                    Value::scalar(1f64),
                    Value::scalar(2f64),
                    Value::scalar(3f64),
                    Value::scalar(4f64),
                ])
            )
            .unwrap(),
            Value::scalar(5f64)
        );
    }

    #[test]
    fn unit_default() {
        assert_eq!(
            liquid_core::call_filter!(Default, "", "bar").unwrap(),
            liquid_core::value!("bar")
        );
        assert_eq!(
            liquid_core::call_filter!(Default, "foo", "bar").unwrap(),
            liquid_core::value!("foo")
        );
        assert_eq!(
            liquid_core::call_filter!(Default, 0_f64, "bar").unwrap(),
            Value::scalar(0_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Default, liquid_core::value!([]), 1_f64).unwrap(),
            Value::scalar(1_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Default, liquid_core::value!([""]), 1_f64).unwrap(),
            liquid_core::value!([""])
        );
        assert_eq!(
            liquid_core::call_filter!(Default, Object::new(), 1_f64).unwrap(),
            Value::scalar(1_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Default, false, Value::scalar(1_f64)).unwrap(),
            Value::scalar(1_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Default, true, Value::scalar(1_f64)).unwrap(),
            Value::scalar(true)
        );
    }
}
