use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{
    Display_filter, Filter, FilterParameters, FilterReflection, FromFilterParameters, ParseFilter,
};
use liquid_core::{Value, ValueView};

use crate::invalid_input;

// shopify-specific

#[derive(Debug, FilterParameters)]
struct PluralizeArgs {
    #[parameter(description = "The singular version of the string.")]
    singular: Expression,
    #[parameter(description = "The plural version of the string.")]
    plural: Expression,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "pluralize",
    description = "Outputs the singular or plural version of a string based on the value of the input.",
    parameters(PluralizeArgs),
    parsed(PluralizeFilter)
)]
pub struct Pluralize;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "pluralize"]
struct PluralizeFilter {
    #[parameters]
    args: PluralizeArgs,
}

impl Filter for PluralizeFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let n = input
            .as_scalar()
            .and_then(|s| s.to_integer())
            .ok_or_else(|| invalid_input("Whole number expected"))?;

        if (n as isize) == 1 {
            Ok(args.singular.to_value())
        } else {
            Ok(args.plural.to_value())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_pluralize() {
        assert_eq!(
            liquid_core::call_filter!(Pluralize, 1i64, "one", "many").unwrap(),
            liquid_core::value!("one")
        );

        assert_eq!(
            liquid_core::call_filter!(Pluralize, 0i64, "one", "many").unwrap(),
            liquid_core::value!("many")
        );

        assert_eq!(
            liquid_core::call_filter!(Pluralize, 2i64, "one", "many").unwrap(),
            liquid_core::value!("many")
        );

        assert_eq!(
            liquid_core::call_filter!(Pluralize, 10i64, "one", "many").unwrap(),
            liquid_core::value!("many")
        );
    }
}
