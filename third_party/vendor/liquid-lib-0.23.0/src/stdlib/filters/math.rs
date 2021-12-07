use std::convert::TryInto;

use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

use crate::{invalid_argument, invalid_input};

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "abs",
    description = "Returns the absolute value of a number.",
    parsed(AbsFilter)
)]
pub struct Abs;

#[derive(Debug, Default, Display_filter)]
#[name = "abs"]
struct AbsFilter;

impl Filter for AbsFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;
        input
            .to_integer()
            .map(|i| Value::scalar(i.abs()))
            .or_else(|| input.to_float().map(|i| Value::scalar(i.abs())))
            .ok_or_else(|| invalid_input("Number expected"))
    }
}

#[derive(Debug, FilterParameters)]
struct AtLeastArgs {
    #[parameter(description = "The lower limit of the input.")]
    min: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "at_least",
    description = "Limits a number to a minimum value.",
    parameters(AtLeastArgs),
    parsed(AtLeastFilter)
)]
pub struct AtLeast;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "at_least"]
struct AtLeastFilter {
    #[parameters]
    args: AtLeastArgs,
}

impl Filter for AtLeastFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let min = args
            .min
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        let result = input
            .to_integer()
            .and_then(|i| min.to_integer().map(|min| Value::scalar(i.max(min))))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| min.to_float().map(|min| Value::scalar(i.max(min))))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct AtMostArgs {
    #[parameter(description = "The upper limit of the input.")]
    max: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "at_most",
    description = "Limits a number to a maximum value.",
    parameters(AtMostArgs),
    parsed(AtMostFilter)
)]
pub struct AtMost;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "at_most"]
struct AtMostFilter {
    #[parameters]
    args: AtMostArgs,
}

impl Filter for AtMostFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let max = args
            .max
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        let result = input
            .to_integer()
            .and_then(|i| max.to_integer().map(|max| Value::scalar(i.min(max))))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| max.to_float().map(|max| Value::scalar(i.min(max))))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct PlusArgs {
    #[parameter(description = "The number to sum to the input.")]
    operand: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "plus",
    description = "Sums a number with the given operand.",
    parameters(PlusArgs),
    parsed(PlusFilter)
)]
pub struct Plus;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "plus"]
struct PlusFilter {
    #[parameters]
    args: PlusArgs,
}

impl Filter for PlusFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let operand = args
            .operand
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        let result = input
            .to_integer()
            .and_then(|i| operand.to_integer().map(|o| Value::scalar(i + o)))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| operand.to_float().map(|o| Value::scalar(i + o)))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct MinusArgs {
    #[parameter(description = "The number to subtract to the input.")]
    operand: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "minus",
    description = "Subtracts the given operand from a number.",
    parameters(MinusArgs),
    parsed(MinusFilter)
)]
pub struct Minus;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "minus"]
struct MinusFilter {
    #[parameters]
    args: MinusArgs,
}

impl Filter for MinusFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let operand = args
            .operand
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        let result = input
            .to_integer()
            .and_then(|i| operand.to_integer().map(|o| Value::scalar(i - o)))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| operand.to_float().map(|o| Value::scalar(i - o)))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct TimesArgs {
    #[parameter(description = "The number to multiply the input by.")]
    operand: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "times",
    description = "Multiplies a number by the given operand.",
    parameters(TimesArgs),
    parsed(TimesFilter)
)]
pub struct Times;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "times"]
struct TimesFilter {
    #[parameters]
    args: TimesArgs,
}

impl Filter for TimesFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let operand = args
            .operand
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        let result = input
            .to_integer()
            .and_then(|i| operand.to_integer().map(|o| Value::scalar(i * o)))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| operand.to_float().map(|o| Value::scalar(i * o)))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct DividedByArgs {
    #[parameter(description = "The number to divide the input by.")]
    operand: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "divided_by",
    description = "Divides a number by the given operand.",
    parameters(DividedByArgs),
    parsed(DividedByFilter)
)]
pub struct DividedBy;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "divided_by"]
struct DividedByFilter {
    #[parameters]
    args: DividedByArgs,
}

impl Filter for DividedByFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let operand = args
            .operand
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        if let Some(o) = operand.to_integer() {
            if o == 0 {
                return Err(invalid_argument("operand", "Can't divide by zero"));
            }
        } else if let Some(o) = operand.to_float() {
            if o == 0.0 {
                return Err(invalid_argument("operand", "Can't divide by zero"));
            }
        }

        let result = input
            .to_integer()
            .and_then(|i| operand.to_integer().map(|o| Value::scalar(i / o)))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| operand.to_float().map(|o| Value::scalar(i / o)))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct ModuloArgs {
    #[parameter(description = "The modulo of the input. Must be a number.")]
    operand: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "modulo",
    description = "The remainder of a division operation of a number by the given operand.",
    parameters(ModuloArgs),
    parsed(ModuloFilter)
)]
pub struct Modulo;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "modulo"]
struct ModuloFilter {
    #[parameters]
    args: ModuloArgs,
}

impl Filter for ModuloFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_scalar()
            .ok_or_else(|| invalid_input("Number expected"))?;

        let operand = args
            .operand
            .as_scalar()
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        if let Some(o) = operand.to_integer() {
            if o == 0 {
                return Err(invalid_argument("operand", "Can't divide by zero"));
            }
        } else if let Some(o) = operand.to_float() {
            if o == 0.0 {
                return Err(invalid_argument("operand", "Can't divide by zero"));
            }
        }

        let result = input
            .to_integer()
            .and_then(|i| operand.to_integer().map(|o| Value::scalar(i % o)))
            .or_else(|| {
                input
                    .to_float()
                    .and_then(|i| operand.to_float().map(|o| Value::scalar(i % o)))
            })
            .ok_or_else(|| invalid_argument("operand", "Number expected"))?;

        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct RoundArgs {
    #[parameter(
        description = "Number of decimal places. Defaults to 0 (nearest integer).",
        arg_type = "integer"
    )]
    decimal_places: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "round",
    description = "Rounds an input number to the nearest integer or, if a number is specified as an argument, to that number of decimal places.",
    parameters(RoundArgs),
    parsed(RoundFilter)
)]
pub struct Round;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "round"]
struct RoundFilter {
    #[parameters]
    args: RoundArgs,
}

impl Filter for RoundFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let n = args.decimal_places.unwrap_or(0);

        let input = input
            .as_scalar()
            .and_then(|s| s.to_float())
            .ok_or_else(|| invalid_input("Number expected"))?;

        match n.cmp(&0) {
            std::cmp::Ordering::Equal => Ok(Value::scalar(input.round() as i64)),
            std::cmp::Ordering::Less => Ok(Value::scalar(input.round() as i64)),
            _ => {
                let multiplier = 10.0_f64.powi(
                    n.try_into()
                        .map_err(|_| invalid_input("decimal-places was too large"))?,
                );
                Ok(Value::scalar((input * multiplier).round() / multiplier))
            }
        }
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "ceil",
    description = "Rounds the input up to the nearest whole number.",
    parsed(CeilFilter)
)]
pub struct Ceil;

#[derive(Debug, Default, Display_filter)]
#[name = "ceil"]
struct CeilFilter;

impl Filter for CeilFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let n = input
            .as_scalar()
            .and_then(|s| s.to_float())
            .ok_or_else(|| invalid_input("Number expected"))?;
        Ok(Value::scalar(n.ceil() as i64))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "floor",
    description = "Rounds a number down to the nearest whole number.",
    parsed(FloorFilter)
)]
pub struct Floor;

#[derive(Debug, Default, Display_filter)]
#[name = "floor"]
struct FloorFilter;

impl Filter for FloorFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let n = input
            .as_scalar()
            .and_then(|s| s.to_float())
            .ok_or_else(|| invalid_input("Number expected"))?;
        Ok(Value::scalar(n.floor() as i64))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_abs() {
        assert_eq!(
            liquid_core::call_filter!(Abs, -1f64).unwrap(),
            Value::scalar(1f64)
        );
    }

    #[test]
    fn unit_abs_positive_in_string() {
        assert_eq!(
            liquid_core::call_filter!(Abs, "42").unwrap(),
            Value::scalar(42f64)
        );
    }

    #[test]
    fn unit_abs_not_number_or_string() {
        liquid_core::call_filter!(Abs, true).unwrap_err();
    }

    #[test]
    fn unit_abs_one_argument() {
        liquid_core::call_filter!(Abs, -1f64, 0f64).unwrap_err();
    }

    #[test]
    fn unit_abs_shopify_liquid() {
        // Three tests from https://shopify.github.io/liquid/filters/abs/
        assert_eq!(
            liquid_core::call_filter!(Abs, -17f64).unwrap(),
            Value::scalar(17f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Abs, 4f64).unwrap(),
            Value::scalar(4f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Abs, "-19.86").unwrap(),
            Value::scalar(19.86f64)
        );
    }
    #[test]
    fn unit_at_least() {
        assert_eq!(
            liquid_core::call_filter!(AtLeast, 4f64, 5f64).unwrap(),
            Value::scalar(5f64)
        );
        assert_eq!(
            liquid_core::call_filter!(AtLeast, 4f64, 3f64).unwrap(),
            Value::scalar(4f64)
        );
        assert_eq!(
            liquid_core::call_filter!(AtLeast, 21.5, 2.25).unwrap(),
            Value::scalar(21.5)
        );
        assert_eq!(
            liquid_core::call_filter!(AtLeast, 21.5, 42.25).unwrap(),
            Value::scalar(42.25)
        );
    }
    #[test]
    fn unit_at_most() {
        assert_eq!(
            liquid_core::call_filter!(AtMost, 4f64, 5f64).unwrap(),
            Value::scalar(4f64)
        );
        assert_eq!(
            liquid_core::call_filter!(AtMost, 4f64, 3f64).unwrap(),
            Value::scalar(3f64)
        );
        assert_eq!(
            liquid_core::call_filter!(AtMost, 21.5, 2.25).unwrap(),
            Value::scalar(2.25)
        );
        assert_eq!(
            liquid_core::call_filter!(AtMost, 21.5, 42.25).unwrap(),
            Value::scalar(21.5)
        );
    }
    #[test]
    fn unit_plus() {
        assert_eq!(
            liquid_core::call_filter!(Plus, 2f64, 1f64).unwrap(),
            Value::scalar(3f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Plus, 21.5, 2.25).unwrap(),
            Value::scalar(23.75)
        );
    }

    #[test]
    fn unit_minus() {
        assert_eq!(
            liquid_core::call_filter!(Minus, 2f64, 1f64).unwrap(),
            Value::scalar(1f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Minus, 21.5, 1.25).unwrap(),
            Value::scalar(20.25)
        );
    }

    #[test]
    fn unit_times() {
        assert_eq!(
            liquid_core::call_filter!(Times, 2f64, 3f64).unwrap(),
            Value::scalar(6f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Times, 8.5, 0.5).unwrap(),
            Value::scalar(4.25)
        );
        liquid_core::call_filter!(Times, true, 8.5).unwrap_err();
        liquid_core::call_filter!(Times, 2.5, true).unwrap_err();
        liquid_core::call_filter!(Times, 2.5).unwrap_err();
    }

    #[test]
    fn unit_modulo() {
        assert_eq!(
            liquid_core::call_filter!(Modulo, 3_f64, 2_f64).unwrap(),
            Value::scalar(1_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Modulo, 3_f64, 3.0).unwrap(),
            Value::scalar(0_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Modulo, 24_f64, 7_f64).unwrap(),
            Value::scalar(3_f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Modulo, 183.357, 12_f64).unwrap(),
            Value::scalar(3.3569999999999993)
        );
    }

    #[test]
    fn unit_divided_by() {
        assert_eq!(
            liquid_core::call_filter!(DividedBy, 4f64, 2f64).unwrap(),
            Value::scalar(2f64)
        );
        assert_eq!(
            liquid_core::call_filter!(DividedBy, 5f64, 2f64).unwrap(),
            Value::scalar(2.5f64)
        );
        liquid_core::call_filter!(DividedBy, true, 8.5).unwrap_err();
        liquid_core::call_filter!(DividedBy, 2.5, true).unwrap_err();
        liquid_core::call_filter!(DividedBy, 2.5).unwrap_err();
    }

    #[test]
    fn unit_ceil() {
        assert_eq!(
            liquid_core::call_filter!(Ceil, 1.1f64).unwrap(),
            Value::scalar(2f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Ceil, 1f64).unwrap(),
            Value::scalar(1f64)
        );
        liquid_core::call_filter!(Ceil, true).unwrap_err();
    }

    #[test]
    fn unit_floor() {
        assert_eq!(
            liquid_core::call_filter!(Floor, 1.1f64).unwrap(),
            Value::scalar(1f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Floor, 1f64).unwrap(),
            Value::scalar(1f64)
        );
        liquid_core::call_filter!(Floor, true).unwrap_err();
    }

    #[test]
    fn unit_round() {
        assert_eq!(
            liquid_core::call_filter!(Round, 1.1f64).unwrap(),
            Value::scalar(1i64)
        );
        assert_eq!(
            liquid_core::call_filter!(Round, 1.5f64).unwrap(),
            Value::scalar(2i64)
        );
        assert_eq!(
            liquid_core::call_filter!(Round, 2f64).unwrap(),
            Value::scalar(2i64)
        );
        liquid_core::call_filter!(Round, true).unwrap_err();
    }

    #[test]
    fn unit_round_precision() {
        assert_eq!(
            liquid_core::call_filter!(Round, 1.1f64, 0i64).unwrap(),
            Value::scalar(1f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Round, 1.5f64, 1i64).unwrap(),
            Value::scalar(1.5f64)
        );
        assert_eq!(
            liquid_core::call_filter!(Round, 1.23456f64, 3i64).unwrap(),
            Value::scalar(1.235f64)
        );
    }
}
