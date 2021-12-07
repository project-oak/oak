use std::cmp;

use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

use crate::invalid_argument;

fn canonicalize_slice(
    slice_offset: isize,
    slice_length: isize,
    vec_length: usize,
) -> (usize, usize) {
    let vec_length = vec_length as isize;

    // Cap slice_offset
    let slice_offset = cmp::min(slice_offset, vec_length);
    // Reverse indexing
    let slice_offset = if slice_offset < 0 {
        slice_offset + vec_length
    } else {
        slice_offset
    };

    // Cap slice_length
    let slice_length = if slice_offset + slice_length > vec_length {
        vec_length - slice_offset
    } else {
        slice_length
    };

    (slice_offset as usize, slice_length as usize)
}

#[derive(Debug, FilterParameters)]
struct SliceArgs {
    #[parameter(description = "The offset of the slice.", arg_type = "integer")]
    offset: Expression,

    #[parameter(description = "The length of the slice.", arg_type = "integer")]
    length: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "slice",
    description = "Takes a slice of a given string or array.",
    parameters(SliceArgs),
    parsed(SliceFilter)
)]
pub struct Slice;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "slice"]
struct SliceFilter {
    #[parameters]
    args: SliceArgs,
}

impl Filter for SliceFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let offset = args.offset as isize;
        let length = args.length.unwrap_or(1) as isize;

        if length < 1 {
            return invalid_argument("length", "Positive number expected").into_err();
        }

        if let Some(input) = input.as_array() {
            let (offset, length) = canonicalize_slice(offset, length, input.size() as usize);
            Ok(Value::array(
                input
                    .values()
                    .skip(offset)
                    .take(length)
                    .map(|s| s.to_value()),
            ))
        } else {
            let input = input.to_kstr();
            let (offset, length) = canonicalize_slice(offset, length, input.len());
            Ok(Value::scalar(
                input.chars().skip(offset).take(length).collect::<String>(),
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_slice() {
        assert_eq!(
            liquid_core::call_filter!(
                Slice,
                "I often quote myself.  It adds spice to my conversation.",
                2,
                3
            )
            .unwrap(),
            liquid_core::value!("oft")
        );
    }

    #[test]
    fn unit_slice_no_length_specified() {
        assert_eq!(
            liquid_core::call_filter!(
                Slice,
                "I often quote myself.  It adds spice to my conversation.",
                4
            )
            .unwrap(),
            liquid_core::value!("t")
        );
    }

    #[test]
    fn unit_slice_negative_offset() {
        assert_eq!(
            liquid_core::call_filter!(
                Slice,
                "I often quote myself.  It adds spice to my conversation.",
                -10,
                3
            )
            .unwrap(),
            liquid_core::value!("ver")
        );
    }

    #[test]
    fn unit_slice_non_positive_length() {
        liquid_core::call_filter!(
            Slice,
            "I often quote myself.  It adds spice to my conversation.",
            -10,
            0
        )
        .unwrap_err();
        liquid_core::call_filter!(
            Slice,
            "I often quote myself.  It adds spice to my conversation.",
            -10,
            -1
        )
        .unwrap_err();
    }
}
