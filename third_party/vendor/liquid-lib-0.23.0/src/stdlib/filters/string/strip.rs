use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};
use liquid_core::{Value, ValueView};

/// Removes all whitespace (tabs, spaces, and newlines) from both the left and right side of a
/// string.
///
/// It does not affect spaces between words.  Note that while this works for the case of tabs,
/// spaces, and newlines, it also removes any other codepoints defined by the Unicode Derived Core
/// Property `White_Space` (per [rust
/// documentation](https://doc.rust-lang.org/std/primitive.str.html#method.trim_start).
#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "strip",
    description = "Removes all whitespace (tabs, spaces, and newlines) from both the left and right side of a string.",
    parsed(StripFilter)
)]
pub struct Strip;

#[derive(Debug, Default, Display_filter)]
#[name = "strip"]
struct StripFilter;

impl Filter for StripFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let input = input.to_kstr();
        Ok(Value::scalar(input.trim().to_owned()))
    }
}

/// Removes all whitespaces (tabs, spaces, and newlines) from the beginning of a string.
///
/// The filter does not affect spaces between words.  Note that while this works for the case of
/// tabs, spaces, and newlines, it also removes any other codepoints defined by the Unicode Derived
/// Core Property `White_Space` (per [rust
/// documentation](https://doc.rust-lang.org/std/primitive.str.html#method.trim_start).
#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "lstrip",
    description = "Removes all whitespaces (tabs, spaces, and newlines) from the beginning of a string.",
    parsed(LstripFilter)
)]
pub struct Lstrip;

#[derive(Debug, Default, Display_filter)]
#[name = "lstrip"]
struct LstripFilter;

impl Filter for LstripFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let input = input.to_kstr();
        Ok(Value::scalar(input.trim_start().to_owned()))
    }
}

/// Removes all whitespace (tabs, spaces, and newlines) from the right side of a string.
///
/// The filter does not affect spaces between words.  Note that while this works for the case of
/// tabs, spaces, and newlines, it also removes any other codepoints defined by the Unicode Derived
/// Core Property `White_Space` (per [rust
/// documentation](https://doc.rust-lang.org/std/primitive.str.html#method.trim_start).
#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "rstrip",
    description = "Removes all whitespace (tabs, spaces, and newlines) from the right side of a string.",
    parsed(RstripFilter)
)]
pub struct Rstrip;

#[derive(Debug, Default, Display_filter)]
#[name = "rstrip"]
struct RstripFilter;

impl Filter for RstripFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let input = input.to_kstr();
        Ok(Value::scalar(input.trim_end().to_owned()))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "strip_newlines",
    description = "Removes any newline characters (line breaks) from a string.",
    parsed(StripNewlinesFilter)
)]
pub struct StripNewlines;

#[derive(Debug, Default, Display_filter)]
#[name = "strip_newlines"]
struct StripNewlinesFilter;

impl Filter for StripNewlinesFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let input = input.to_kstr();
        Ok(Value::scalar(
            input
                .chars()
                .filter(|c| *c != '\n' && *c != '\r')
                .collect::<String>(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_lstrip() {
        assert_eq!(
            liquid_core::call_filter!(Lstrip, " 	 \n \r test").unwrap(),
            liquid_core::value!("test")
        );
    }

    #[test]
    fn unit_lstrip_non_string() {
        assert_eq!(
            liquid_core::call_filter!(Lstrip, 0f64).unwrap(),
            liquid_core::value!("0")
        );
    }

    #[test]
    fn unit_lstrip_one_argument() {
        liquid_core::call_filter!(Lstrip, " 	 \n \r test", 0f64).unwrap_err();
    }

    #[test]
    fn unit_lstrip_shopify_liquid() {
        // One test from https://shopify.github.io/liquid/filters/lstrip/
        assert_eq!(
            liquid_core::call_filter!(Lstrip, "          So much room for activities!          ")
                .unwrap(),
            liquid_core::value!("So much room for activities!          ")
        );
    }

    #[test]
    fn unit_lstrip_trailing_sequence() {
        assert_eq!(
            liquid_core::call_filter!(Lstrip, " 	 \n \r test 	 \n \r ").unwrap(),
            liquid_core::value!("test 	 \n \r ")
        );
    }

    #[test]
    fn unit_lstrip_trailing_sequence_only() {
        assert_eq!(
            liquid_core::call_filter!(Lstrip, "test 	 \n \r ").unwrap(),
            liquid_core::value!("test 	 \n \r ")
        );
    }

    #[test]
    fn unit_rstrip() {
        assert_eq!(
            liquid_core::call_filter!(Rstrip, "test 	 \n \r ").unwrap(),
            liquid_core::value!("test")
        );
    }

    #[test]
    fn unit_rstrip_leading_sequence() {
        assert_eq!(
            liquid_core::call_filter!(Rstrip, " 	 \n \r test 	 \n \r ").unwrap(),
            liquid_core::value!(" 	 \n \r test")
        );
    }

    #[test]
    fn unit_rstrip_leading_sequence_only() {
        assert_eq!(
            liquid_core::call_filter!(Rstrip, " 	 \n \r test").unwrap(),
            liquid_core::value!(" 	 \n \r test")
        );
    }

    #[test]
    fn unit_rstrip_non_string() {
        assert_eq!(
            liquid_core::call_filter!(Rstrip, 0f64).unwrap(),
            liquid_core::value!("0")
        );
    }

    #[test]
    fn unit_rstrip_one_argument() {
        liquid_core::call_filter!(Rstrip, " 	 \n \r test", 0f64).unwrap_err();
    }

    #[test]
    fn unit_rstrip_shopify_liquid() {
        // One test from https://shopify.github.io/liquid/filters/rstrip/
        assert_eq!(
            liquid_core::call_filter!(Rstrip, "          So much room for activities!          ")
                .unwrap(),
            liquid_core::value!("          So much room for activities!")
        );
    }

    #[test]
    fn unit_strip() {
        assert_eq!(
            liquid_core::call_filter!(Strip, " 	 \n \r test 	 \n \r ").unwrap(),
            liquid_core::value!("test")
        );
    }

    #[test]
    fn unit_strip_leading_sequence_only() {
        assert_eq!(
            liquid_core::call_filter!(Strip, " 	 \n \r test").unwrap(),
            liquid_core::value!("test")
        );
    }

    #[test]
    fn unit_strip_non_string() {
        assert_eq!(
            liquid_core::call_filter!(Strip, 0f64).unwrap(),
            liquid_core::value!("0")
        );
    }

    #[test]
    fn unit_strip_one_argument() {
        liquid_core::call_filter!(Strip, " 	 \n \r test 	 \n \r ", 0f64).unwrap_err();
    }

    #[test]
    fn unit_strip_shopify_liquid() {
        // One test from https://shopify.github.io/liquid/filters/strip/
        assert_eq!(
            liquid_core::call_filter!(Strip, "          So much room for activities!          ")
                .unwrap(),
            liquid_core::value!("So much room for activities!")
        );
    }

    #[test]
    fn unit_strip_trailing_sequence_only() {
        assert_eq!(
            liquid_core::call_filter!(Strip, "test 	 \n \r ").unwrap(),
            liquid_core::value!("test")
        );
    }

    #[test]
    fn unit_strip_newlines() {
        assert_eq!(
            liquid_core::call_filter!(StripNewlines, "a\nb\n").unwrap(),
            liquid_core::value!("ab")
        );
    }

    #[test]
    fn unit_strip_newlines_between_only() {
        assert_eq!(
            liquid_core::call_filter!(StripNewlines, "a\nb").unwrap(),
            liquid_core::value!("ab")
        );
    }

    #[test]
    fn unit_strip_newlines_leading_only() {
        assert_eq!(
            liquid_core::call_filter!(StripNewlines, "\nab").unwrap(),
            liquid_core::value!("ab")
        );
    }

    #[test]
    fn unit_strip_newlines_non_string() {
        assert_eq!(
            liquid_core::call_filter!(StripNewlines, 0f64).unwrap(),
            liquid_core::value!("0")
        );
    }

    #[test]
    fn unit_strip_newlines_one_argument() {
        liquid_core::call_filter!(StripNewlines, "ab\n", 0f64).unwrap_err();
    }

    #[test]
    fn unit_strip_newlines_shopify_liquid() {
        // Test from https://shopify.github.io/liquid/filters/strip_newlines/
        assert_eq!(
            liquid_core::call_filter!(StripNewlines, "\nHello\nthere\n").unwrap(),
            liquid_core::value!("Hellothere")
        );
    }

    #[test]
    fn unit_strip_newlines_trailing_only() {
        assert_eq!(
            liquid_core::call_filter!(StripNewlines, "ab\n").unwrap(),
            liquid_core::value!("ab")
        );
    }
}
