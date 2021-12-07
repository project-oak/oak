use std::fmt::Write;

use liquid_core::Expression;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Error, Result};
use liquid_core::{Value, ValueView};

#[derive(Debug, FilterParameters)]
struct DateArgs {
    #[parameter(description = "The format to return the date in.", arg_type = "str")]
    format: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "date",
    description = "Converts a timestamp into another date format.",
    parameters(DateArgs),
    parsed(DateFilter)
)]
pub struct Date;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "date"]
struct DateFilter {
    #[parameters]
    args: DateArgs,
}

impl Filter for DateFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let date = input.as_scalar().and_then(|s| s.to_date_time());
        match date {
            Some(date) if !args.format.is_empty() => {
                let d = date.format(args.format.as_str());
                let s = try_to_string(d).ok_or_else(|| {
                    Error::with_msg(format!("Invalid date-format string: {}", args.format))
                })?;
                Ok(Value::scalar(s))
            }
            _ => Ok(input.to_value()),
        }
    }
}

fn try_to_string(f: impl std::fmt::Display) -> Option<String> {
    let mut buf = String::new();
    buf.write_fmt(format_args!("{}", f)).ok()?;
    buf.shrink_to_fit();
    Some(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_date() {
        assert_eq!(
            liquid_core::call_filter!(Date, "13 Jun 2016 02:30:00 +0300", "%Y-%m-%d").unwrap(),
            liquid_core::value!("2016-06-13")
        );
    }

    #[test]
    fn unit_date_invalid_format() {
        liquid_core::call_filter!(Date, "13 Jun 2016 02:30:00 +0300", "%Y %h %8").unwrap_err();
    }

    #[test]
    fn unit_date_cobalt_format() {
        assert_eq!(
            liquid_core::call_filter!(Date, "2016-06-13 02:30:00 +0300", "%Y-%m-%d").unwrap(),
            liquid_core::value!("2016-06-13")
        );
    }

    #[test]
    fn unit_date_bad_input_type() {
        assert_eq!(
            liquid_core::call_filter!(Date, 0f64, "%Y-%m-%d").unwrap(),
            Value::scalar(0f64)
        );
    }

    #[test]
    fn unit_date_bad_input_format() {
        assert_eq!(
            liquid_core::call_filter!(Date, "blah blah blah", "%Y-%m-%d").unwrap(),
            liquid_core::value!("blah blah blah")
        );
    }

    #[test]
    fn unit_date_format_empty() {
        assert_eq!(
            liquid_core::call_filter!(Date, "13 Jun 2016 02:30:00 +0300", "").unwrap(),
            liquid_core::value!("13 Jun 2016 02:30:00 +0300")
        );
    }

    #[test]
    fn unit_date_bad_format_type() {
        assert_eq!(
            liquid_core::call_filter!(Date, "13 Jun 2016 02:30:00 +0300", 0f64).unwrap(),
            liquid_core::value!("0")
        );
    }

    #[test]
    fn unit_date_missing_format() {
        liquid_core::call_filter!(Date, "13 Jun 2016 02:30:00 +0300").unwrap_err();
    }

    #[test]
    fn unit_date_extra_param() {
        liquid_core::call_filter!(Date, "13 Jun 2016 02:30:00 +0300", 0f64, 1f64).unwrap_err();
    }
}
