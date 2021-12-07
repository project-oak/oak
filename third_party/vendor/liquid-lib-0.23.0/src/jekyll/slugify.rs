use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};
use regex::Regex;

#[derive(PartialEq)]
enum SlugifyMode {
    No,
    Def,
    Raw,
    Pretty,
    Ascii,
    Latin,
}

impl SlugifyMode {
    fn new(mode_str: &str) -> SlugifyMode {
        match mode_str {
            "none" => SlugifyMode::No,
            "raw" => SlugifyMode::Raw,
            "pretty" => SlugifyMode::Pretty,
            "ascii" => SlugifyMode::Ascii,
            "latin" => SlugifyMode::Latin,
            _ => SlugifyMode::Def,
        }
    }
}

static SLUG_INVALID_CHARS_DEFAULT: once_cell::sync::Lazy<Regex> =
    once_cell::sync::Lazy::new(|| Regex::new(r"([^0-9\p{Alphabetic}]+)").unwrap());
static SLUG_INVALID_CHARS_RAW: once_cell::sync::Lazy<Regex> =
    once_cell::sync::Lazy::new(|| Regex::new(r"([\s]+)").unwrap());
static SLUG_INVALID_CHARS_PRETTY: once_cell::sync::Lazy<Regex> = once_cell::sync::Lazy::new(|| {
    Regex::new(r"([^\p{Alphabetic}0-9\._\~!\$&'\(\)\+,;=@]+)").unwrap()
});
static SLUG_INVALID_CHARS_ASCII: once_cell::sync::Lazy<Regex> =
    once_cell::sync::Lazy::new(|| Regex::new(r"([^a-zA-Z0-9]+)").unwrap());

#[derive(Debug, FilterParameters)]
struct SlugifyArgs {
    #[parameter(
        description = "The slugify mode. May be \"none\", \"raw\", \"pretty\", \"ascii\", \"latin\" or \"default\".",
        arg_type = "str"
    )]
    mode: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "slugify",
    description = "Convert a string into a lowercase URL \"slug\".",
    parameters(SlugifyArgs),
    parsed(SlugifyFilter)
)]
pub struct Slugify;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "slugify"]
struct SlugifyFilter {
    #[parameters]
    args: SlugifyArgs,
}

impl Filter for SlugifyFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let s = input.to_kstr();
        let mode = args
            .mode
            .map(|mode| SlugifyMode::new(mode.as_str()))
            .unwrap_or(SlugifyMode::Def);

        let s = if mode == SlugifyMode::Latin {
            deunicode::deunicode_with_tofu(&s.trim(), "-")
        } else {
            s.trim().to_string()
        };

        let result = match mode {
            SlugifyMode::No => s,
            SlugifyMode::Def => SLUG_INVALID_CHARS_DEFAULT.replace_all(&s, "-").to_string(),
            SlugifyMode::Raw => SLUG_INVALID_CHARS_RAW.replace_all(&s, "-").to_string(),
            SlugifyMode::Pretty => SLUG_INVALID_CHARS_PRETTY.replace_all(&s, "-").to_string(),
            SlugifyMode::Ascii | SlugifyMode::Latin => {
                SLUG_INVALID_CHARS_ASCII.replace_all(&s, "-").to_string()
            }
        };

        Ok(Value::scalar(result.trim_matches('-').to_lowercase()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slugify_default() {
        assert_eq!(
            liquid_core::call_filter!(Slugify, "The _cönfig.yml file").unwrap(),
            liquid_core::value!("the-cönfig-yml-file")
        );
    }

    #[test]
    fn test_slugify_ascii() {
        assert_eq!(
            liquid_core::call_filter!(Slugify, "The _cönfig.yml file", "ascii").unwrap(),
            liquid_core::value!("the-c-nfig-yml-file")
        );
    }

    #[test]
    fn test_slugify_latin() {
        assert_eq!(
            liquid_core::call_filter!(Slugify, "The _cönfig.yml file", "latin").unwrap(),
            liquid_core::value!("the-config-yml-file")
        );
    }

    #[test]
    fn test_slugify_raw() {
        assert_eq!(
            liquid_core::call_filter!(Slugify, "The _config.yml file", "raw").unwrap(),
            liquid_core::value!("the-_config.yml-file")
        );
    }

    #[test]
    fn test_slugify_none() {
        assert_eq!(
            liquid_core::call_filter!(Slugify, "The _config.yml file", "none").unwrap(),
            liquid_core::value!("the _config.yml file")
        );
    }
}
