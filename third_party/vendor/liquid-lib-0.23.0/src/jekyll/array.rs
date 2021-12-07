use std::fmt::Write;

use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

use crate::invalid_input;

#[derive(Debug, FilterParameters)]
struct PushArgs {
    #[parameter(description = "The element to append to the array.")]
    element: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "push",
    description = "Appends the given element to the end of an array.",
    parameters(PushArgs),
    parsed(PushFilter)
)]
pub struct Push;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "push"]
struct PushFilter {
    #[parameters]
    args: PushArgs,
}

impl Filter for PushFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let element = args.element.to_value();
        let mut array = input
            .to_value()
            .into_array()
            .ok_or_else(|| invalid_input("Array expected"))?;
        array.push(element);

        Ok(Value::Array(array))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "pop",
    description = "Removes the last element of an array.",
    parsed(PopFilter)
)]
pub struct Pop;

#[derive(Debug, Default, Display_filter)]
#[name = "pop"]
struct PopFilter;

impl Filter for PopFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let mut array = input
            .to_value()
            .into_array()
            .ok_or_else(|| invalid_input("Array expected"))?;
        array.pop();

        Ok(Value::Array(array))
    }
}

#[derive(Debug, FilterParameters)]
struct UnshiftArgs {
    #[parameter(description = "The element to append to the array.")]
    element: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "unshift",
    description = "Appends the given element to the start of an array.",
    parameters(UnshiftArgs),
    parsed(UnshiftFilter)
)]
pub struct Unshift;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "unshift"]
struct UnshiftFilter {
    #[parameters]
    args: UnshiftArgs,
}

impl Filter for UnshiftFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let element = args.element.to_value();
        let mut array = input
            .to_value()
            .into_array()
            .ok_or_else(|| invalid_input("Array expected"))?;
        array.insert(0, element);

        Ok(Value::Array(array))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "shift",
    description = "Removes the first element of an array.",
    parsed(ShiftFilter)
)]
pub struct Shift;

#[derive(Debug, Default, Display_filter)]
#[name = "shift"]
struct ShiftFilter;

impl Filter for ShiftFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let mut array = input
            .to_value()
            .into_array()
            .ok_or_else(|| invalid_input("Array expected"))?;

        if !array.is_empty() {
            array.remove(0);
        }

        Ok(Value::Array(array))
    }
}

#[derive(Debug, FilterParameters)]
struct ArrayToSentenceStringArgs {
    #[parameter(
        description = "The connector between the last two elements. Defaults to \"and\".",
        arg_type = "str"
    )]
    connector: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "array_to_sentence_string",
    description = "Converts an array into a sentence. This sentence will be a list of the elements of the array separated by comma, with a connector between the last two elements.",
    parameters(ArrayToSentenceStringArgs),
    parsed(ArrayToSentenceStringFilter)
)]
pub struct ArrayToSentenceString;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "array_to_sentence_string"]
struct ArrayToSentenceStringFilter {
    #[parameters]
    args: ArrayToSentenceStringArgs,
}

impl Filter for ArrayToSentenceStringFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let connector = args.connector.unwrap_or_else(|| "and".into());

        let mut array = input
            .as_array()
            .ok_or_else(|| invalid_input("Array expected"))?
            .values();

        let mut sentence = array
            .next()
            .map(|v| v.to_kstr().into_string())
            .unwrap_or_else(|| "".to_string());

        let mut iter = array.peekable();
        while let Some(value) = iter.next() {
            if iter.peek().is_some() {
                write!(sentence, ", {}", value.render())
                    .expect("It should be safe to write to a string.");
            } else {
                write!(sentence, ", {} {}", connector, value.render())
                    .expect("It should be safe to write to a string.");
            }
        }

        Ok(Value::scalar(sentence))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_push() {
        let input = liquid_core::value!(["Seattle", "Tacoma"]);
        let unit_result = liquid_core::call_filter!(Push, input, "Spokane").unwrap();
        let desired_result = liquid_core::value!(["Seattle", "Tacoma", "Spokane",]);
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_pop() {
        let input = liquid_core::value!(["Seattle", "Tacoma"]);
        let unit_result = liquid_core::call_filter!(Pop, input).unwrap();
        let desired_result = liquid_core::value!(["Seattle"]);
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_pop_empty() {
        let input = liquid_core::value!([]);
        let unit_result = liquid_core::call_filter!(Pop, input).unwrap();
        let desired_result = liquid_core::value!([]);
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_unshift() {
        let input = liquid_core::value!(["Seattle", "Tacoma"]);
        let unit_result = liquid_core::call_filter!(Unshift, input, "Olympia").unwrap();
        let desired_result = liquid_core::value!(["Olympia", "Seattle", "Tacoma"]);
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_shift() {
        let input = liquid_core::value!(["Seattle", "Tacoma"]);
        let unit_result = liquid_core::call_filter!(Shift, input).unwrap();
        let desired_result = liquid_core::value!(["Tacoma"]);
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_shift_empty() {
        let input = liquid_core::value!([]);
        let unit_result = liquid_core::call_filter!(Shift, input).unwrap();
        let desired_result = liquid_core::value!([]);
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_array_to_sentence_string() {
        let input = liquid_core::value!(["foo", "bar", "baz"]);
        let unit_result = liquid_core::call_filter!(ArrayToSentenceString, input).unwrap();
        let desired_result = "foo, bar, and baz";
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_array_to_sentence_string_two_elements() {
        let input = liquid_core::value!(["foo", "bar"]);
        let unit_result = liquid_core::call_filter!(ArrayToSentenceString, input).unwrap();
        let desired_result = "foo, and bar";
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_array_to_sentence_string_one_element() {
        let input = liquid_core::value!(["foo"]);
        let unit_result = liquid_core::call_filter!(ArrayToSentenceString, input).unwrap();
        let desired_result = "foo";
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_array_to_sentence_string_no_elements() {
        let input = liquid_core::value!([]);
        let unit_result = liquid_core::call_filter!(ArrayToSentenceString, input).unwrap();
        let desired_result = "";
        assert_eq!(unit_result, desired_result);
    }

    #[test]
    fn unit_array_to_sentence_string_custom_connector() {
        let input = liquid_core::value!(["foo", "bar", "baz"]);
        let unit_result = liquid_core::call_filter!(ArrayToSentenceString, input, "or").unwrap();
        let desired_result = "foo, bar, or baz";
        assert_eq!(unit_result, desired_result);
    }
}
