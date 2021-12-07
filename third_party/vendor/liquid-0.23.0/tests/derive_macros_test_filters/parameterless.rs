use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};
use liquid_core::{Value, ValueView};

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "no_args",
    description = "Filter with no arguments.",
    parsed(TestParameterlessFilter)
)]
pub struct TestParameterlessFilterParser;

#[derive(Debug, Default, Display_filter)]
#[name = "no_args"]
pub struct TestParameterlessFilter;

impl Filter for TestParameterlessFilter {
    fn evaluate(&self, _input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        let result = "<>";

        Ok(Value::scalar(result))
    }
}
