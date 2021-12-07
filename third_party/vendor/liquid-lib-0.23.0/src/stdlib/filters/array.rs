use std::cmp;

use liquid_core::model::ValueViewCmp;
use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueCow, ValueView};

use crate::{invalid_argument, invalid_input};

fn as_sequence<'k>(input: &'k dyn ValueView) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
    if let Some(array) = input.as_array() {
        array.values()
    } else if input.is_nil() {
        Box::new(vec![].into_iter())
    } else {
        Box::new(std::iter::once(input))
    }
}

#[derive(Debug, FilterParameters)]
struct JoinArgs {
    #[parameter(
        description = "The separator between each element in the string.",
        arg_type = "str"
    )]
    separator: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "join",
    description = "Combines the items in an array into a single string using the argument as a separator.",
    parameters(JoinArgs),
    parsed(JoinFilter)
)]
pub struct Join;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "join"]
struct JoinFilter {
    #[parameters]
    args: JoinArgs,
}

impl Filter for JoinFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let separator = args.separator.unwrap_or_else(|| " ".into());

        let input = input
            .as_array()
            .ok_or_else(|| invalid_input("Array of strings expected"))?;
        let input = input.values().map(|x| x.to_kstr());

        Ok(Value::scalar(itertools::join(input, separator.as_str())))
    }
}

fn nil_safe_compare(a: &dyn ValueView, b: &dyn ValueView) -> Option<cmp::Ordering> {
    if a.is_nil() && b.is_nil() {
        Some(cmp::Ordering::Equal)
    } else if a.is_nil() {
        Some(cmp::Ordering::Greater)
    } else if b.is_nil() {
        Some(cmp::Ordering::Less)
    } else {
        ValueViewCmp::new(a).partial_cmp(&ValueViewCmp::new(b))
    }
}

fn nil_safe_casecmp_key(value: &dyn ValueView) -> Option<String> {
    if value.is_nil() {
        None
    } else {
        Some(value.to_kstr().to_lowercase())
    }
}

fn nil_safe_casecmp(a: &Option<String>, b: &Option<String>) -> Option<cmp::Ordering> {
    match (a, b) {
        (None, None) => Some(cmp::Ordering::Equal),
        (None, _) => Some(cmp::Ordering::Greater),
        (_, None) => Some(cmp::Ordering::Less),
        (a, b) => a.partial_cmp(b),
    }
}

#[derive(Debug, Default, FilterParameters)]
struct PropertyArgs {
    #[parameter(description = "The property accessed by the filter.", arg_type = "str")]
    property: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "sort",
    description = "Sorts items in an array. The order of the sorted array is case-sensitive.",
    parameters(PropertyArgs),
    parsed(SortFilter)
)]
pub struct Sort;

#[derive(Debug, Default, FromFilterParameters, Display_filter)]
#[name = "sort"]
struct SortFilter {
    #[parameters]
    args: PropertyArgs,
}

fn safe_property_getter<'a>(value: &'a Value, property: &str) -> &'a dyn ValueView {
    value
        .as_object()
        .and_then(|obj| obj.get(property))
        .unwrap_or(&Value::Nil)
}

impl Filter for SortFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input: Vec<_> = as_sequence(input).collect();
        if args.property.is_some() && !input.iter().all(|v| v.is_object()) {
            return Err(invalid_input("Array of objects expected"));
        }

        let mut sorted: Vec<Value> = input.iter().map(|v| v.to_value()).collect();
        if let Some(property) = &args.property {
            // Using unwrap is ok since all of the elements are objects
            sorted.sort_by(|a, b| {
                nil_safe_compare(
                    safe_property_getter(a, property),
                    safe_property_getter(b, property),
                )
                .unwrap_or(cmp::Ordering::Equal)
            });
        } else {
            sorted.sort_by(|a, b| nil_safe_compare(a, b).unwrap_or(cmp::Ordering::Equal));
        }
        Ok(Value::array(sorted))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "sort_natural",
    description = "Sorts items in an array.",
    parameters(PropertyArgs),
    parsed(SortNaturalFilter)
)]
pub struct SortNatural;

#[derive(Debug, Default, FromFilterParameters, Display_filter)]
#[name = "sort_natural"]
struct SortNaturalFilter {
    #[parameters]
    args: PropertyArgs,
}

impl Filter for SortNaturalFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input: Vec<_> = as_sequence(input).collect();
        if args.property.is_some() && !input.iter().all(|v| v.is_object()) {
            return Err(invalid_input("Array of objects expected"));
        }

        let mut sorted: Vec<_> = if let Some(property) = &args.property {
            input
                .iter()
                .map(|v| v.to_value())
                .map(|v| {
                    (
                        nil_safe_casecmp_key(&safe_property_getter(&v, property).to_value()),
                        v,
                    )
                })
                .collect()
        } else {
            input
                .iter()
                .map(|v| v.to_value())
                .map(|v| (nil_safe_casecmp_key(&v), v))
                .collect()
        };
        sorted.sort_by(|a, b| nil_safe_casecmp(&a.0, &b.0).unwrap_or(cmp::Ordering::Equal));
        let result: Vec<_> = sorted.into_iter().map(|(_, v)| v).collect();
        Ok(Value::array(result))
    }
}

#[derive(Debug, FilterParameters)]
struct WhereArgs {
    #[parameter(description = "The property being matched", arg_type = "str")]
    property: Expression,
    #[parameter(
        description = "The value the property is matched with",
        arg_type = "any"
    )]
    target_value: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "where",
    description = "Filter the elements of an array to those with a certain property value. \
                   By default the target is any truthy value.",
    parameters(WhereArgs),
    parsed(WhereFilter)
)]
pub struct Where;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "where"]
struct WhereFilter {
    #[parameters]
    args: WhereArgs,
}

impl Filter for WhereFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;
        let property: &str = &args.property;
        let target_value: Option<ValueCow<'_>> = args.target_value;

        if let Some(array) = input.as_array() {
            if !array.values().all(|v| v.is_object()) {
                return Ok(Value::Nil);
            }
        } else if !input.is_object() {
            return Err(invalid_input(
                "Array of objects or a single object expected",
            ));
        }

        let input = as_sequence(input);
        let array: Vec<_> = match target_value {
            None => input
                .filter_map(|v| v.as_object())
                .filter(|object| {
                    object
                        .get(property)
                        .map_or(false, |v| v.query_state(liquid_core::model::State::Truthy))
                })
                .map(|object| object.to_value())
                .collect(),
            Some(target_value) => input
                .filter_map(|v| v.as_object())
                .filter(|object| {
                    object.get(property).map_or(false, |value| {
                        let value = ValueViewCmp::new(value);
                        target_value == value
                    })
                })
                .map(|object| object.to_value())
                .collect(),
        };
        Ok(Value::array(array))
    }
}

/// Removes any duplicate elements in an array.
///
/// This has an O(n^2) worst-case complexity.
#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "uniq",
    description = "Removes any duplicate elements in an array.",
    parsed(UniqFilter)
)]
pub struct Uniq;

#[derive(Debug, Default, Display_filter)]
#[name = "uniq"]
struct UniqFilter;

impl Filter for UniqFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        // TODO(#267) optional property parameter

        let array = input
            .as_array()
            .ok_or_else(|| invalid_input("Array expected"))?;
        let mut deduped: Vec<Value> = Vec::with_capacity(array.size() as usize);
        for x in array.values() {
            if deduped
                .iter()
                .find(|v| ValueViewCmp::new(v.as_view()) == ValueViewCmp::new(x))
                .is_none()
            {
                deduped.push(x.to_value())
            }
        }
        Ok(Value::array(deduped))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "reverse",
    description = "Reverses the order of the items in an array.",
    parsed(ReverseFilter)
)]
pub struct Reverse;

#[derive(Debug, Default, Display_filter)]
#[name = "reverse"]
struct ReverseFilter;

impl Filter for ReverseFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let mut array: Vec<_> = input
            .as_array()
            .ok_or_else(|| invalid_input("Array expected"))?
            .values()
            .map(|v| v.to_value())
            .collect();
        array.reverse();
        Ok(Value::array(array))
    }
}

#[derive(Debug, FilterParameters)]
struct MapArgs {
    #[parameter(
        description = "The property to be extracted from the values in the input.",
        arg_type = "str"
    )]
    property: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "map",
    description = "Extract `property` from the `Value::Object` elements of an array.",
    parameters(MapArgs),
    parsed(MapFilter)
)]
pub struct Map;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "map"]
struct MapFilter {
    #[parameters]
    args: MapArgs,
}

impl Filter for MapFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let array = input
            .as_array()
            .ok_or_else(|| invalid_input("Array expected"))?;

        let result: Vec<_> = array
            .values()
            .filter_map(|v| {
                v.as_object()
                    .and_then(|v| v.get(&args.property))
                    .map(|v| v.to_value())
            })
            .collect();
        Ok(Value::array(result))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "compact",
    description = "Remove nulls from an iterable.",
    parameters(PropertyArgs),
    parsed(CompactFilter)
)]
pub struct Compact;

#[derive(Debug, Default, FromFilterParameters, Display_filter)]
#[name = "compact"]
struct CompactFilter {
    #[parameters]
    args: PropertyArgs,
}

impl Filter for CompactFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let array = input
            .as_array()
            .ok_or_else(|| invalid_input("Array expected"))?;

        let result: Vec<_> = if let Some(property) = &args.property {
            if !array.values().all(|v| v.is_object()) {
                return Err(invalid_input("Array of objects expected"));
            }
            // Reject non objects that don't have the required property
            array
                .values()
                .filter(|v| {
                    !v.as_object()
                        .and_then(|obj| obj.get(property.as_str()))
                        .map_or(true, |v| v.is_nil())
                })
                .map(|v| v.to_value())
                .collect()
        } else {
            array
                .values()
                .filter(|v| !v.is_nil())
                .map(|v| v.to_value())
                .collect()
        };

        Ok(Value::array(result))
    }
}

#[derive(Debug, FilterParameters)]
struct ConcatArgs {
    #[parameter(description = "The array to concatenate the input with.")]
    array: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "concat",
    description = "Concatenates the input array with a given array.",
    parameters(ConcatArgs),
    parsed(ConcatFilter)
)]
pub struct Concat;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "concat"]
struct ConcatFilter {
    #[parameters]
    args: ConcatArgs,
}

impl Filter for ConcatFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input
            .as_array()
            .ok_or_else(|| invalid_input("Array expected"))?;
        let input = input.values().map(|v| v.to_value());

        let array = args
            .array
            .as_array()
            .ok_or_else(|| invalid_argument("array", "Array expected"))?;
        let array = array.values().map(|v| v.to_value());

        let result = input.chain(array);
        let result: Vec<_> = result.collect();
        Ok(Value::array(result))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "first",
    description = "Returns the first item of an array.",
    parsed(FirstFilter)
)]
pub struct First;

#[derive(Debug, Default, Display_filter)]
#[name = "first"]
struct FirstFilter;

impl Filter for FirstFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        if let Some(x) = input.as_scalar() {
            let c = x
                .to_kstr()
                .chars()
                .next()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "".to_owned());
            Ok(Value::scalar(c))
        } else if let Some(x) = input.as_array() {
            Ok(x.first()
                .map(|v| v.to_value())
                .unwrap_or_else(|| Value::Nil))
        } else {
            Err(invalid_input("String or Array expected"))
        }
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "last",
    description = "Returns the last item of an array.",
    parsed(LastFilter)
)]
pub struct Last;

#[derive(Debug, Default, Display_filter)]
#[name = "last"]
struct LastFilter;

impl Filter for LastFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        if let Some(x) = input.as_scalar() {
            let c = x
                .to_kstr()
                .chars()
                .last()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "".to_owned());
            Ok(Value::scalar(c))
        } else if let Some(x) = input.as_array() {
            Ok(x.last().map(|v| v.to_value()).unwrap_or_else(|| Value::Nil))
        } else {
            Err(invalid_input("String or Array expected"))
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn unit_concat_nothing() {
        let input = liquid_core::value!([1f64, 2f64]);
        let result = liquid_core::value!([1f64, 2f64]);
        assert_eq!(
            liquid_core::call_filter!(Concat, input, liquid_core::value!([])).unwrap(),
            result
        );
    }

    #[test]
    fn unit_concat_something() {
        let input = liquid_core::value!([1f64, 2f64]);
        let result = liquid_core::value!([1f64, 2f64, 3f64, 4f64]);
        assert_eq!(
            liquid_core::call_filter!(Concat, input, liquid_core::value!([3f64, 4f64])).unwrap(),
            result
        );
    }

    #[test]
    fn unit_concat_mixed() {
        let input = liquid_core::value!([1f64, 2f64]);
        let result = liquid_core::value!([1f64, 2f64, 3f64, "a"]);
        assert_eq!(
            liquid_core::call_filter!(Concat, input, liquid_core::value!([3f64, "a"])).unwrap(),
            result
        );
    }

    #[test]
    fn unit_concat_wrong_type() {
        let input = liquid_core::value!([1f64, 2f64]);
        liquid_core::call_filter!(Concat, input, 1f64).unwrap_err();
    }

    #[test]
    fn unit_concat_no_args() {
        let input = liquid_core::value!([1f64, 2f64]);
        liquid_core::call_filter!(Concat, input).unwrap_err();
    }

    #[test]
    fn unit_concat_extra_args() {
        let input = liquid_core::value!([1f64, 2f64]);
        liquid_core::call_filter!(Concat, input, liquid_core::value!([3f64, "a"]), 2f64)
            .unwrap_err();
    }

    #[test]
    #[allow(clippy::float_cmp)] // Need to dig into this
    fn unit_first() {
        assert_eq!(
            liquid_core::call_filter!(First, liquid_core::value!([0f64, 1f64, 2f64, 3f64, 4f64,]))
                .unwrap(),
            0f64
        );
        assert_eq!(
            liquid_core::call_filter!(First, liquid_core::value!(["test", "two"])).unwrap(),
            liquid_core::value!("test")
        );
        assert_eq!(
            liquid_core::call_filter!(First, liquid_core::value!([])).unwrap(),
            Value::Nil
        );
    }

    #[test]
    fn unit_join() {
        let input = liquid_core::value!(["a", "b", "c"]);
        assert_eq!(
            liquid_core::call_filter!(Join, input, ",").unwrap(),
            liquid_core::value!("a,b,c")
        );
    }

    #[test]
    fn unit_join_bad_input() {
        let input = "a";
        liquid_core::call_filter!(Join, input, ",").unwrap_err();
    }

    #[test]
    fn unit_join_bad_join_string() {
        let input = liquid_core::value!(["a", "b", "c"]);
        assert_eq!(
            liquid_core::call_filter!(Join, input, 1f64).unwrap(),
            "a1b1c"
        );
    }

    #[test]
    fn unit_join_no_args() {
        let input = liquid_core::value!(["a", "b", "c"]);
        assert_eq!(liquid_core::call_filter!(Join, input).unwrap(), "a b c");
    }

    #[test]
    fn unit_join_non_string_element() {
        let input = liquid_core::value!(["a", 1f64, "c"]);
        assert_eq!(
            liquid_core::call_filter!(Join, input, ",").unwrap(),
            liquid_core::value!("a,1,c")
        );
    }

    #[test]
    fn unit_sort() {
        let input = &liquid_core::value!(["Z", "b", "c", "a"]);
        let desired_result = liquid_core::value!(["Z", "a", "b", "c"]);
        assert_eq!(
            liquid_core::call_filter!(Sort, input).unwrap(),
            desired_result
        );
    }

    #[test]
    fn unit_sort_natural() {
        let input = &liquid_core::value!(["Z", "b", "c", "a"]);
        let desired_result = liquid_core::value!(["a", "b", "c", "Z"]);
        assert_eq!(
            liquid_core::call_filter!(SortNatural, input).unwrap(),
            desired_result
        );
    }

    #[test]
    #[allow(clippy::float_cmp)] // Need to dig into this
    fn unit_last() {
        assert_eq!(
            liquid_core::call_filter!(Last, liquid_core::value!([0f64, 1f64, 2f64, 3f64, 4f64,]))
                .unwrap(),
            4f64
        );
        assert_eq!(
            liquid_core::call_filter!(Last, liquid_core::value!(["test", "last"])).unwrap(),
            liquid_core::value!("last")
        );
        assert_eq!(
            liquid_core::call_filter!(Last, liquid_core::value!([])).unwrap(),
            Value::Nil
        );
    }

    #[test]
    fn unit_reverse_apples_oranges_peaches_plums() {
        // First example from https://shopify.github.io/liquid/filters/reverse/
        let input = liquid_core::value!(["apples", "oranges", "peaches", "plums"]);
        let desired_result = liquid_core::value!(["plums", "peaches", "oranges", "apples"]);
        assert_eq!(
            liquid_core::call_filter!(Reverse, input).unwrap(),
            desired_result
        );
    }

    #[test]
    fn unit_reverse_array() {
        let input = liquid_core::value!([3f64, 1f64, 2f64]);
        let desired_result = liquid_core::value!([2f64, 1f64, 3f64]);
        assert_eq!(
            liquid_core::call_filter!(Reverse, input).unwrap(),
            desired_result
        );
    }

    #[test]
    fn unit_reverse_array_extra_args() {
        let input = liquid_core::value!([3f64, 1f64, 2f64]);
        liquid_core::call_filter!(Reverse, input, 0f64).unwrap_err();
    }

    #[test]
    fn unit_reverse_ground_control_major_tom() {
        // Second example from https://shopify.github.io/liquid/filters/reverse/
        let input = liquid_core::value!([
            "G", "r", "o", "u", "n", "d", " ", "c", "o", "n", "t", "r", "o", "l", " ", "t", "o",
            " ", "M", "a", "j", "o", "r", " ", "T", "o", "m", ".",
        ]);
        let desired_result = liquid_core::value!([
            ".", "m", "o", "T", " ", "r", "o", "j", "a", "M", " ", "o", "t", " ", "l", "o", "r",
            "t", "n", "o", "c", " ", "d", "n", "u", "o", "r", "G",
        ]);
        assert_eq!(
            liquid_core::call_filter!(Reverse, input).unwrap(),
            desired_result
        );
    }

    #[test]
    fn unit_reverse_string() {
        let input = "abc";
        liquid_core::call_filter!(Reverse, input).unwrap_err();
    }

    #[test]
    fn unit_uniq() {
        let input = liquid_core::value!(["a", "b", "a"]);
        let desired_result = liquid_core::value!(["a", "b"]);
        assert_eq!(
            liquid_core::call_filter!(Uniq, input).unwrap(),
            desired_result
        );
    }

    #[test]
    fn unit_uniq_non_array() {
        let input = 0f64;
        liquid_core::call_filter!(Uniq, input).unwrap_err();
    }

    #[test]
    fn unit_uniq_one_argument() {
        let input = liquid_core::value!(["a", "b", "a"]);
        liquid_core::call_filter!(Uniq, input, 0f64).unwrap_err();
    }

    #[test]
    fn unit_uniq_shopify_liquid() {
        // Test from https://shopify.github.io/liquid/filters/uniq/
        let input = liquid_core::value!(["ants", "bugs", "bees", "bugs", "ants",]);
        let desired_result = liquid_core::value!(["ants", "bugs", "bees"]);
        assert_eq!(
            liquid_core::call_filter!(Uniq, input).unwrap(),
            desired_result
        );
    }
}
