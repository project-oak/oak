use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

#[derive(Debug, FilterParameters)]
struct ReplaceArgs {
    #[parameter(description = "The text to search.", arg_type = "str")]
    search: Expression,
    #[parameter(
        description = "The text to replace search results with. If not given, the filter will just delete search results.",
        arg_type = "str"
    )]
    replace: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "replace",
    description = "Replaces the occurrences of the `search` with `replace`. If `replace` is not given, just deletes occurrences of `search`.",
    parameters(ReplaceArgs),
    parsed(ReplaceFilter)
)]
pub struct Replace;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "replace"]
struct ReplaceFilter {
    #[parameters]
    args: ReplaceArgs,
}

impl Filter for ReplaceFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input.to_kstr();

        let replace = args.replace.unwrap_or_else(|| "".into());

        Ok(Value::scalar(
            input.replace(args.search.as_str(), replace.as_str()),
        ))
    }
}

#[derive(Debug, FilterParameters)]
struct ReplaceFirstArgs {
    #[parameter(description = "The text to search.", arg_type = "str")]
    search: Expression,
    #[parameter(
        description = "The text to replace search result with. If not given, the filter will just delete search results«.",
        arg_type = "str"
    )]
    replace: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "replace_first",
    description = "Replaces the first occurrence of the `search` with `replace`. If `replace` is not given, just deletes the occurrence.",
    parameters(ReplaceFirstArgs),
    parsed(ReplaceFirstFilter)
)]
pub struct ReplaceFirst;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "replace_first"]
struct ReplaceFirstFilter {
    #[parameters]
    args: ReplaceFirstArgs,
}

impl Filter for ReplaceFirstFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input.to_kstr();

        let search = args.search;
        let replace = args.replace.unwrap_or_else(|| "".into());

        {
            let tokens: Vec<&str> = input.splitn(2, search.as_str()).collect();
            if tokens.len() == 2 {
                let result = [tokens[0], replace.as_str(), tokens[1]].join("");
                return Ok(Value::scalar(result));
            }
        }
        Ok(Value::scalar(input.into_owned()))
    }
}

#[derive(Debug, FilterParameters)]
struct RemoveArgs {
    #[parameter(description = "The text to remove.", arg_type = "str")]
    search: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "remove",
    description = "Removes all occurrences of the given string.",
    parameters(RemoveArgs),
    parsed(RemoveFilter)
)]
pub struct Remove;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "remove"]
struct RemoveFilter {
    #[parameters]
    args: RemoveArgs,
}

impl Filter for RemoveFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input.to_kstr();

        Ok(Value::scalar(input.replace(args.search.as_str(), "")))
    }
}

#[derive(Debug, FilterParameters)]
struct RemoveFirstArgs {
    #[parameter(description = "The text to remove.", arg_type = "str")]
    search: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "remove_first",
    description = "Removes the first occurrence of the given string.",
    parameters(RemoveFirstArgs),
    parsed(RemoveFirstFilter)
)]
pub struct RemoveFirst;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "remove_first"]
struct RemoveFirstFilter {
    #[parameters]
    args: RemoveFirstArgs,
}

impl Filter for RemoveFirstFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input.to_kstr();

        Ok(Value::scalar(
            input.splitn(2, args.search.as_str()).collect::<String>(),
        ))
    }
}

#[derive(Debug, FilterParameters)]
struct AppendArgs {
    #[parameter(description = "The string to append to the input.", arg_type = "str")]
    string: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "append",
    description = "Appends the given text to a string.",
    parameters(AppendArgs),
    parsed(AppendFilter)
)]
pub struct Append;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "append"]
struct AppendFilter {
    #[parameters]
    args: AppendArgs,
}

impl Filter for AppendFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let mut input = input.to_kstr().into_string();
        input.push_str(args.string.as_str());

        Ok(Value::scalar(input))
    }
}

#[derive(Debug, FilterParameters)]
struct PrependArgs {
    #[parameter(description = "The string to prepend to the input.", arg_type = "str")]
    string: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "prepend",
    description = "Prepends the given text to a string.",
    parameters(PrependArgs),
    parsed(PrependFilter)
)]
pub struct Prepend;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "prepend"]
struct PrependFilter {
    #[parameters]
    args: PrependArgs,
}

impl Filter for PrependFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let input = input.to_kstr();
        let mut string = args.string.into_string();
        string.push_str(input.as_str());

        Ok(Value::scalar(string))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_append() {
        assert_eq!(
            liquid_core::call_filter!(Append, "sam", "son").unwrap(),
            liquid_core::value!("samson")
        );
    }

    #[test]
    fn unit_prepend() {
        assert_eq!(
            liquid_core::call_filter!(Prepend, "barbar", "foo").unwrap(),
            liquid_core::value!("foobarbar")
        );
    }

    #[test]
    fn unit_remove() {
        assert_eq!(
            liquid_core::call_filter!(Remove, "barbar", "bar").unwrap(),
            liquid_core::value!("")
        );
        assert_eq!(
            liquid_core::call_filter!(Remove, "barbar", "").unwrap(),
            liquid_core::value!("barbar")
        );
        assert_eq!(
            liquid_core::call_filter!(Remove, "barbar", "barbar").unwrap(),
            liquid_core::value!("")
        );
        assert_eq!(
            liquid_core::call_filter!(Remove, "barbar", "a").unwrap(),
            liquid_core::value!("brbr")
        );
    }

    #[test]
    fn unit_remove_first() {
        assert_eq!(
            liquid_core::call_filter!(RemoveFirst, "barbar", "bar").unwrap(),
            liquid_core::value!("bar")
        );
        assert_eq!(
            liquid_core::call_filter!(RemoveFirst, "barbar", "").unwrap(),
            liquid_core::value!("barbar")
        );
        assert_eq!(
            liquid_core::call_filter!(RemoveFirst, "barbar", "barbar").unwrap(),
            liquid_core::value!("")
        );
        assert_eq!(
            liquid_core::call_filter!(RemoveFirst, "barbar", "a").unwrap(),
            liquid_core::value!("brbar")
        );
    }

    #[test]
    fn unit_replace() {
        assert_eq!(
            liquid_core::call_filter!(Replace, "barbar", "bar", "foo").unwrap(),
            liquid_core::value!("foofoo")
        );
    }

    #[test]
    fn unit_replace_first() {
        assert_eq!(
            liquid_core::call_filter!(ReplaceFirst, "barbar", "bar", "foo").unwrap(),
            liquid_core::value!("foobar")
        );
        assert_eq!(
            liquid_core::call_filter!(ReplaceFirst, "barxoxo", "xo", "foo").unwrap(),
            liquid_core::value!("barfooxo")
        );
        assert_eq!(
            liquid_core::call_filter!(ReplaceFirst, "", "bar", "foo").unwrap(),
            liquid_core::value!("")
        );
    }
}
