use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

pub mod case;
pub mod operate;
pub mod strip;
pub mod truncate;

#[derive(Debug, FilterParameters)]
struct SplitArgs {
    #[parameter(
        description = "The separator between each element in the string.",
        arg_type = "str"
    )]
    pattern: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "split",
    description = "Divides an input string into an array using the argument as a separator.",
    parameters(SplitArgs),
    parsed(SplitFilter)
)]
pub struct Split;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "split"]
struct SplitFilter {
    #[parameters]
    args: SplitArgs,
}

impl Filter for SplitFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input.to_kstr();

        if input.is_empty() {
            Ok(Value::Array(Vec::new()))
        } else {
            // Split and construct resulting Array
            Ok(Value::Array(
                input
                    .split(args.pattern.as_str())
                    .map(|s| Value::scalar(s.to_owned()))
                    .collect(),
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_split() {
        assert_eq!(
            liquid_core::call_filter!(Split, "a, b, c", ", ").unwrap(),
            liquid_core::value!(["a", "b", "c"])
        );
        assert_eq!(
            liquid_core::call_filter!(Split, "a~b", "~").unwrap(),
            liquid_core::value!(["a", "b"])
        );
    }

    #[test]
    fn unit_split_bad_split_string() {
        assert_eq!(
            liquid_core::call_filter!(Split, "a,b,c", 1f64).unwrap(),
            liquid_core::value!(["a,b,c"])
        );
    }

    #[test]
    fn unit_split_no_args() {
        liquid_core::call_filter!(Split, "a,b,c").unwrap_err();
    }
}
