use std::cmp;

use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};
use unicode_segmentation::UnicodeSegmentation;

#[derive(Debug, FilterParameters)]
struct TruncateArgs {
    #[parameter(
        description = "The maximum length of the string, after which it will be truncated.",
        arg_type = "integer"
    )]
    length: Option<Expression>,

    #[parameter(
        description = "The text appended to the end of the string if it is truncated. This text counts to the maximum length of the string. Defaults to \"...\".",
        arg_type = "str"
    )]
    ellipsis: Option<Expression>,
}

/// `truncate` shortens a string down to the number of characters passed as a parameter.
///
/// Note that this function operates on [grapheme
/// clusters](http://www.unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries) (or *user-perceived
/// character*), rather than Unicode code points.  Each grapheme cluster may be composed of more
/// than one Unicode code point, and does not necessarily correspond to rust's conception of a
/// character.
///
/// If the number of characters specified is less than the length of the string, an ellipsis
/// (`...`) is appended to the string and is included in the character count.
///
/// ## Custom ellipsis
///
/// `truncate` takes an optional second parameter that specifies the sequence of characters to be
/// appended to the truncated string. By default this is an ellipsis (`...`), but you can specify a
/// different sequence.
///
/// The length of the second parameter counts against the number of characters specified by the
/// first parameter. For example, if you want to truncate a string to exactly 10 characters, and
/// use a 3-character ellipsis, use 13 for the first parameter of `truncate`, since the ellipsis
/// counts as 3 characters.
///
/// ## No ellipsis
///
/// You can truncate to the exact number of characters specified by the first parameter and show no
/// trailing characters by passing a blank string as the second parameter.
#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "truncate",
    description = "Shortens a string down to the number of characters passed as a parameter.",
    parameters(TruncateArgs),
    parsed(TruncateFilter)
)]
pub struct Truncate;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "truncate"]
struct TruncateFilter {
    #[parameters]
    args: TruncateArgs,
}

impl Filter for TruncateFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let length = args.length.unwrap_or(50) as usize;
        let truncate_string = args.ellipsis.unwrap_or_else(|| "...".into());
        let diff = if length >= truncate_string.len() {
            length - truncate_string.len()
        } else {
            0
        };
        let l = cmp::max(diff, 0);

        let input_string = input.to_kstr();
        let result = if length < input_string.len() {
            let result = UnicodeSegmentation::graphemes(input_string.as_str(), true)
                .take(l)
                .collect::<Vec<&str>>()
                .join("")
                + truncate_string.as_str();
            Value::scalar(result)
        } else {
            input.to_value()
        };
        Ok(result)
    }
}

#[derive(Debug, FilterParameters)]
struct TruncateWordsArgs {
    #[parameter(
        description = "The maximum number of words, after which the string will be truncated.",
        arg_type = "integer"
    )]
    length: Option<Expression>,

    #[parameter(
        description = "The text appended to the end of the string if it is truncated. This text counts to the maximum word-count of the string. Defaults to \"...\".",
        arg_type = "str"
    )]
    ellipsis: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "truncatewords",
    description = "Shortens a string down to the number of characters passed as a parameter.",
    parameters(TruncateWordsArgs),
    parsed(TruncateWordsFilter)
)]
pub struct TruncateWords;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "truncate"]
struct TruncateWordsFilter {
    #[parameters]
    args: TruncateWordsArgs,
}

impl Filter for TruncateWordsFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let words = args.length.unwrap_or(50) as usize;

        let truncate_string = args.ellipsis.unwrap_or_else(|| "...".into());

        let l = cmp::max(words, 0);

        let input_string = input.to_kstr();

        let word_list: Vec<&str> = input_string.split(' ').collect();
        let result = if words < word_list.len() {
            let result = itertools::join(word_list.iter().take(l), " ") + truncate_string.as_str();
            Value::scalar(result)
        } else {
            input.to_value()
        };
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_truncate() {
        assert_eq!(
            liquid_core::call_filter!(
                Truncate,
                "I often quote myself.  It adds spice to my conversation.",
                17i64
            )
            .unwrap(),
            liquid_core::value!("I often quote ...")
        );
    }

    #[test]
    fn unit_truncate_negative_length() {
        assert_eq!(
            liquid_core::call_filter!(
                Truncate,
                "I often quote myself.  It adds spice to my conversation.",
                -17i64
            )
            .unwrap(),
            liquid_core::value!("I often quote myself.  It adds spice to my conversation.")
        );
    }

    #[test]
    fn unit_truncate_non_string() {
        assert_eq!(
            liquid_core::call_filter!(Truncate, 10000000f64, 5i64).unwrap(),
            liquid_core::value!("10...")
        );
    }

    #[test]
    fn unit_truncate_shopify_liquid() {
        // Tests from https://shopify.github.io/liquid/filters/truncate/
        let input = "Ground control to Major Tom.";

        assert_eq!(
            liquid_core::call_filter!(Truncate, input, 20i64).unwrap(),
            liquid_core::value!("Ground control to...")
        );

        assert_eq!(
            liquid_core::call_filter!(Truncate, input, 25i64, ", and so on").unwrap(),
            liquid_core::value!("Ground control, and so on")
        );

        assert_eq!(
            liquid_core::call_filter!(Truncate, input, 20i64, "").unwrap(),
            liquid_core::value!("Ground control to Ma")
        );
    }

    #[test]
    fn unit_truncate_three_arguments() {
        liquid_core::call_filter!(
            Truncate,
            "I often quote myself.  It adds spice to my conversation.",
            17i64,
            "...",
            0i64
        )
        .unwrap_err();
    }

    #[test]
    fn unit_truncate_unicode_codepoints_examples() {
        // The examples below came from the unicode_segmentation documentation.
        //
        // https://unicode-rs.github.io/unicode-segmentation/unicode_segmentation/ ...
        //               ...  trait.UnicodeSegmentation.html#tymethod.graphemes
        //
        // Note that the accents applied to each letter are treated as part of the single grapheme
        // cluster for the applicable letter.
        assert_eq!(
            liquid_core::call_filter!(
                Truncate,
                "Here is an a\u{310}, e\u{301}, and o\u{308}\u{332}.",
                20i64
            )
            .unwrap(),
            liquid_core::value!("Here is an a\u{310}, e\u{301}, ...")
        );

        // Note that the 🇷🇺🇸🇹 is treated as a single grapheme cluster.
        assert_eq!(
            liquid_core::call_filter!(Truncate, "Here is a RUST: 🇷🇺🇸🇹.", 20i64).unwrap(),
            liquid_core::value!("Here is a RUST: 🇷🇺...")
        );
    }

    #[test]
    fn unit_truncate_zero_arguments() {
        assert_eq!(
            liquid_core::call_filter!(
                Truncate,
                "I often quote myself.  It adds spice to my conversation."
            )
            .unwrap(),
            liquid_core::value!("I often quote myself.  It adds spice to my conv...")
        );
    }

    #[test]
    fn unit_truncatewords_negative_length() {
        assert_eq!(
            liquid_core::call_filter!(TruncateWords, "one two three", -1_i64).unwrap(),
            liquid_core::value!("one two three")
        );
    }

    #[test]
    fn unit_truncatewords_zero_length() {
        assert_eq!(
            liquid_core::call_filter!(TruncateWords, "one two three", 0_i64).unwrap(),
            liquid_core::value!("...")
        );
    }

    #[test]
    fn unit_truncatewords_no_truncation() {
        assert_eq!(
            liquid_core::call_filter!(TruncateWords, "one two three", 4_i64).unwrap(),
            liquid_core::value!("one two three")
        );
    }

    #[test]
    fn unit_truncatewords_truncate() {
        assert_eq!(
            liquid_core::call_filter!(TruncateWords, "one two three", 2_i64).unwrap(),
            liquid_core::value!("one two...")
        );
        assert_eq!(
            liquid_core::call_filter!(TruncateWords, "one two three", 2_i64, 1_i64).unwrap(),
            liquid_core::value!("one two1")
        );
    }

    #[test]
    fn unit_truncatewords_empty_string() {
        assert_eq!(
            liquid_core::call_filter!(TruncateWords, "", 1_i64).unwrap(),
            liquid_core::value!("")
        );
    }
}
