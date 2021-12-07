use std::convert::TryInto;

use chrono::FixedOffset;
use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

use crate::invalid_input;

// liquid-rust proprietary

#[derive(Debug, FilterParameters)]
struct DateInTzArgs {
    #[parameter(description = "The format to return the date in.", arg_type = "str")]
    format: Expression,
    #[parameter(
        description = "The timezone to convert the date to.",
        arg_type = "integer"
    )]
    timezone: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "date_in_tz",
    description = "Converts a timestamp into another date format and timezone.",
    parameters(DateInTzArgs),
    parsed(DateInTzFilter)
)]
pub struct DateInTz;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "date_in_tz"]
struct DateInTzFilter {
    #[parameters]
    args: DateInTzArgs,
}

impl Filter for DateInTzFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let date = input
            .as_scalar()
            .and_then(|s| s.to_date_time())
            .ok_or_else(|| invalid_input("Invalid date format"))?;

        let timezone = FixedOffset::east(
            (args.timezone * 3600)
                .try_into()
                .map_err(|_| invalid_input("Timezone was too large"))?,
        );

        let formatter = date.with_timezone(&timezone).format(args.format.as_str());
        let date = formatter.to_string();
        Ok(Value::scalar(date))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_date_in_tz_same_day() {
        let unit_result = liquid_core::call_filter!(
            DateInTz,
            "13 Jun 2016 12:00:00 +0000",
            "%Y-%m-%d %H:%M:%S %z",
            3i64
        )
        .unwrap();
        let desired_result = liquid_core::value!("2016-06-13 15:00:00 +0300");
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_date_in_tz_previous_day() {
        let unit_result = liquid_core::call_filter!(
            DateInTz,
            "13 Jun 2016 12:00:00 +0000",
            "%Y-%m-%d %H:%M:%S %z",
            -13i64
        )
        .unwrap();
        let desired_result = liquid_core::value!("2016-06-12 23:00:00 -1300");
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_date_in_tz_next_day() {
        let unit_result = liquid_core::call_filter!(
            DateInTz,
            "13 Jun 2016 12:00:00 +0000",
            "%Y-%m-%d %H:%M:%S %z",
            13i64
        )
        .unwrap();
        let desired_result = liquid_core::value!("2016-06-14 01:00:00 +1300");
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_date_in_tz_input_not_a_string() {
        liquid_core::call_filter!(DateInTz, 0f64, "%Y-%m-%d %H:%M:%S %z", 0i64).unwrap_err();
    }

    #[test]
    fn unit_date_in_tz_input_not_a_date_string() {
        liquid_core::call_filter!(DateInTz, "blah blah blah", "%Y-%m-%d %H:%M:%S %z", 0i64)
            .unwrap_err();
    }

    #[test]
    fn unit_date_in_tz_offset_not_a_num() {
        liquid_core::call_filter!(
            DateInTz,
            "13 Jun 2016 12:00:00 +0000",
            "%Y-%m-%d %H:%M:%S %z",
            "Hello"
        )
        .unwrap_err();
    }

    #[test]
    fn unit_date_in_tz_zero_arguments() {
        liquid_core::call_filter!(DateInTz, "13 Jun 2016 12:00:00 +0000").unwrap_err();
    }

    #[test]
    fn unit_date_in_tz_one_argument() {
        liquid_core::call_filter!(
            DateInTz,
            "13 Jun 2016 12:00:00 +0000",
            "%Y-%m-%d %H:%M:%S %z"
        )
        .unwrap_err();
    }

    #[test]
    fn unit_date_in_tz_three_arguments() {
        liquid_core::call_filter!(
            DateInTz,
            "13 Jun 2016 12:00:00 +0000",
            "%Y-%m-%d %H:%M:%S %z",
            0f64,
            1f64
        )
        .unwrap_err();
    }
}
