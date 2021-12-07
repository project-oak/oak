#![allow(clippy::zero_width_space)]

use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};
use liquid_core::{Value, ValueView};

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "downcase",
    description = "Makes each character in a string downcase.",
    parsed(DowncaseFilter)
)]
pub struct Downcase;

#[derive(Debug, Default, Display_filter)]
#[name = "downcase"]
struct DowncaseFilter;

impl Filter for DowncaseFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let s = input.to_kstr();
        Ok(Value::scalar(s.to_lowercase()))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "upcase",
    description = "Makes each character in a string uppercase.",
    parsed(UpcaseFilter)
)]
pub struct Upcase;

#[derive(Debug, Default, Display_filter)]
#[name = "upcase"]
struct UpcaseFilter;

impl Filter for UpcaseFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let s = input.to_kstr();
        Ok(Value::scalar(s.to_uppercase()))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "capitalize",
    description = "Makes the first character of a string capitalized.",
    parsed(CapitalizeFilter)
)]
pub struct Capitalize;

#[derive(Debug, Default, Display_filter)]
#[name = "capitalize"]
struct CapitalizeFilter;

impl Filter for CapitalizeFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let s = input.to_kstr().to_owned();
        let mut chars = s.chars();
        let capitalized = match chars.next() {
            Some(first_char) => first_char.to_uppercase().chain(chars).collect(),
            None => String::new(),
        };

        Ok(Value::scalar(capitalized))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_capitalize() {
        assert_eq!(
            liquid_core::call_filter!(Capitalize, "abc").unwrap(),
            liquid_core::value!("Abc")
        );
        assert_eq!(
            liquid_core::call_filter!(Capitalize, "hello world 21").unwrap(),
            liquid_core::value!("Hello world 21")
        );

        // sure that Umlauts work
        assert_eq!(
            liquid_core::call_filter!(Capitalize, "über ètat, y̆es?").unwrap(),
            liquid_core::value!("Über ètat, y̆es?")
        );

        // Weird UTF-8 White space is kept – this is a no-break whitespace!
        assert_eq!(
            liquid_core::call_filter!(Capitalize, "hello world​").unwrap(),
            liquid_core::value!("Hello world​")
        );

        // The uppercase version of some character are more than one character long
        assert_eq!(
            liquid_core::call_filter!(Capitalize, "ßß").unwrap(),
            liquid_core::value!("SSß")
        );
    }

    #[test]
    fn unit_downcase() {
        assert_eq!(
            liquid_core::call_filter!(Downcase, "Abc").unwrap(),
            liquid_core::value!("abc")
        );
        assert_eq!(
            liquid_core::call_filter!(Downcase, "Hello World 21").unwrap(),
            liquid_core::value!("hello world 21")
        );
    }

    #[test]
    fn unit_upcase() {
        assert_eq!(
            liquid_core::call_filter!(Upcase, "abc").unwrap(),
            liquid_core::value!("ABC")
        );
        assert_eq!(
            liquid_core::call_filter!(Upcase, "Hello World 21").unwrap(),
            liquid_core::value!("HELLO WORLD 21")
        );
    }
}
