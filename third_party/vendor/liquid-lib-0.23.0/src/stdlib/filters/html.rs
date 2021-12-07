use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};
use liquid_core::{Value, ValueView};
use regex::Regex;

/// Returns the number of already escaped characters.
fn nr_escaped(text: &str) -> usize {
    for prefix in &["lt;", "gt;", "#39;", "quot;", "amp;"] {
        if text.starts_with(prefix) {
            return prefix.len();
        }
    }
    0
}

// The code is adapted from
// https://github.com/rust-lang/rust/blob/master/src/librustdoc/html/escape.rs
// Retrieved 2016-11-19.
fn escape(input: &dyn ValueView, once_p: bool) -> Result<Value> {
    if input.is_nil() {
        return Ok(Value::Nil);
    }
    let s = input.to_kstr();
    let mut result = String::new();
    let mut last = 0;
    let mut skip = 0;
    for (i, c) in s.char_indices() {
        if skip > 0 {
            skip -= 1;
            continue;
        }
        match c as char {
            '<' | '>' | '\'' | '"' | '&' => {
                result.push_str(&s[last..i]);
                last = i + 1;
                let escaped = match c as char {
                    '<' => "&lt;",
                    '>' => "&gt;",
                    '\'' => "&#39;",
                    '"' => "&quot;",
                    '&' => {
                        if once_p {
                            skip = nr_escaped(&s[last..]);
                        }
                        if skip == 0 {
                            "&amp;"
                        } else {
                            "&"
                        }
                    }
                    _ => unreachable!(),
                };
                result.push_str(escaped);
            }
            _ => {}
        }
    }
    if last < s.len() {
        result.push_str(&s[last..]);
    }
    Ok(Value::scalar(result))
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "escape",
    description = "Escapes a string by replacing characters with escape sequences.",
    parsed(EscapeFilter)
)]
pub struct Escape;

#[derive(Debug, Default, Display_filter)]
#[name = "escape"]
struct EscapeFilter;

impl Filter for EscapeFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        escape(input, false)
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "escape_once",
    description = "Escapes a string without changing existing escaped entities.",
    parsed(EscapeOnceFilter)
)]
pub struct EscapeOnce;

#[derive(Debug, Default, Display_filter)]
#[name = "escape_once"]
struct EscapeOnceFilter;

impl Filter for EscapeOnceFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        escape(input, true)
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "strip_html",
    description = "Removes any HTML tags from a string.",
    parsed(StripHtmlFilter)
)]
pub struct StripHtml;

#[derive(Debug, Default, Display_filter)]
#[name = "strip_html"]
struct StripHtmlFilter;

static MATCHERS: once_cell::sync::Lazy<[Regex; 4]> = once_cell::sync::Lazy::new(|| {
    [
        Regex::new(r"(?is)<script.*?</script>").unwrap(),
        Regex::new(r"(?is)<style.*?</style>").unwrap(),
        Regex::new(r"(?is)<!--.*?-->").unwrap(),
        Regex::new(r"(?is)<.*?>").unwrap(),
    ]
});

impl Filter for StripHtmlFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let input = input.to_kstr().into_string();

        let result = MATCHERS.iter().fold(input, |acc, matcher| {
            matcher.replace_all(&acc, "").into_owned()
        });
        Ok(Value::scalar(result))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "newline_to_br",
    description = "Replaces every newline (`\\n`) with an HTML line break (`<br>`).",
    parsed(NewlineToBrFilter)
)]
pub struct NewlineToBr;

#[derive(Debug, Default, Display_filter)]
#[name = "newline_to_br"]
struct NewlineToBrFilter;

impl Filter for NewlineToBrFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        // TODO handle windows line endings
        let input = input.to_kstr();
        Ok(Value::scalar(input.replace("\n", "<br />\n")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_escape() {
        assert_eq!(
            liquid_core::call_filter!(Escape, "Have you read 'James & the Giant Peach'?").unwrap(),
            liquid_core::value!("Have you read &#39;James &amp; the Giant Peach&#39;?")
        );
        assert_eq!(
            liquid_core::call_filter!(Escape, "Tetsuro Takara").unwrap(),
            liquid_core::value!("Tetsuro Takara")
        );
    }

    #[test]
    fn unit_escape_non_ascii() {
        assert_eq!(
            liquid_core::call_filter!(Escape, "word¹ <br> word¹").unwrap(),
            liquid_core::value!("word¹ &lt;br&gt; word¹")
        );
    }

    #[test]
    fn unit_escape_once() {
        assert_eq!(
            liquid_core::call_filter!(EscapeOnce, "1 < 2 & 3").unwrap(),
            liquid_core::value!("1 &lt; 2 &amp; 3")
        );
        assert_eq!(
            liquid_core::call_filter!(EscapeOnce, "1 &lt; 2 &amp; 3").unwrap(),
            liquid_core::value!("1 &lt; 2 &amp; 3")
        );
        assert_eq!(
            liquid_core::call_filter!(EscapeOnce, "&lt;&gt;&amp;&#39;&quot;&xyz;").unwrap(),
            liquid_core::value!("&lt;&gt;&amp;&#39;&quot;&amp;xyz;")
        );
    }

    #[test]
    fn unit_strip_html() {
        assert_eq!(
            liquid_core::call_filter!(
                StripHtml,
                "<script type=\"text/javascript\">alert('Hi!';</script>",
            )
            .unwrap(),
            liquid_core::value!("")
        );
        assert_eq!(
            liquid_core::call_filter!(
                StripHtml,
                "<SCRIPT type=\"text/javascript\">alert('Hi!';</SCRIPT>",
            )
            .unwrap(),
            liquid_core::value!("")
        );
        assert_eq!(
            liquid_core::call_filter!(StripHtml, "<p>test</p>").unwrap(),
            liquid_core::value!("test")
        );
        assert_eq!(
            liquid_core::call_filter!(StripHtml, "<p id='xxx'>test</p>").unwrap(),
            liquid_core::value!("test")
        );
        assert_eq!(
            liquid_core::call_filter!(StripHtml, "<style type=\"text/css\">cool style</style>",)
                .unwrap(),
            liquid_core::value!("")
        );
        assert_eq!(
            liquid_core::call_filter!(StripHtml, "<p\nclass='loooong'>test</p>").unwrap(),
            liquid_core::value!("test")
        );
        assert_eq!(
            liquid_core::call_filter!(StripHtml, "<!--\n\tcomment\n-->test").unwrap(),
            liquid_core::value!("test")
        );
        assert_eq!(
            liquid_core::call_filter!(StripHtml, "").unwrap(),
            liquid_core::value!("")
        );
    }

    #[test]
    fn unit_newline_to_br() {
        assert_eq!(
            liquid_core::call_filter!(NewlineToBr, "a\nb").unwrap(),
            liquid_core::value!("a<br />\nb")
        );
    }

    #[test]
    fn unit_newline_to_br_hello_world() {
        // First example from https://shopify.github.io/liquid/filters/newline_to_br/
        assert_eq!(
            liquid_core::call_filter!(NewlineToBr, "\nHello\nWorld\n").unwrap(),
            liquid_core::value!("<br />\nHello<br />\nWorld<br />\n")
        );
    }

    #[test]
    fn unit_newline_to_br_one_argument() {
        liquid_core::call_filter!(NewlineToBr, "a\nb", 0f64).unwrap_err();
    }
}
