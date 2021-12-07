use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};
use liquid_core::{Value, ValueView};

use crate::invalid_input;

const FRAGMENT: &percent_encoding::AsciiSet = &percent_encoding::NON_ALPHANUMERIC
    .remove(b'-')
    .remove(b'.')
    .remove(b'_');

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "url_encode",
    description = "Converts any URL-unsafe characters in a string into percent-encoded characters.",
    parsed(UrlEncodeFilter)
)]
pub struct UrlEncode;

#[derive(Debug, Default, Display_filter)]
#[name = "url_encode"]
struct UrlEncodeFilter;

impl Filter for UrlEncodeFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        if input.is_nil() {
            return Ok(Value::Nil);
        }

        let s = input.to_kstr();

        let result: String = percent_encoding::utf8_percent_encode(s.as_str(), FRAGMENT).collect();
        Ok(Value::scalar(result))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "url_decode",
    description = "Decodes a string that has been encoded as a URL or by url_encode.",
    parsed(UrlDecodeFilter)
)]
pub struct UrlDecode;

#[derive(Debug, Default, Display_filter)]
#[name = "url_decode"]
struct UrlDecodeFilter;

impl Filter for UrlDecodeFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        if input.is_nil() {
            return Ok(Value::Nil);
        }

        let s = input.to_kstr().replace("+", " ");

        let result = percent_encoding::percent_decode(s.as_bytes())
            .decode_utf8()
            .map_err(|_| invalid_input("Malformed UTF-8"))?
            .into_owned();
        Ok(Value::scalar(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_url_encode() {
        assert_eq!(
            liquid_core::call_filter!(UrlEncode, "foo bar").unwrap(),
            liquid_core::value!("foo%20bar")
        );
        assert_eq!(
            liquid_core::call_filter!(UrlEncode, "foo+1@example.com").unwrap(),
            liquid_core::value!("foo%2B1%40example.com")
        );
    }

    #[test]
    fn unit_url_decode() {
        // TODO Test case from shopify/liquid that we aren't handling:
        // - assert_eq!(
        //      liquid_core::call_filter!(url_decode, "foo+bar").unwrap(),
        //      liquid_core::value!("foo bar")
        //  );
        assert_eq!(
            liquid_core::call_filter!(UrlDecode, "foo%20bar").unwrap(),
            liquid_core::value!("foo bar")
        );
        assert_eq!(
            liquid_core::call_filter!(UrlDecode, "foo%2B1%40example.com").unwrap(),
            liquid_core::value!("foo+1@example.com")
        );
    }
}
