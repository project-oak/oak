use std::io::Write;

use liquid_core::error::ResultLiquidReplaceExt;
use liquid_core::model::{Value, ValueView};
use liquid_core::Language;
use liquid_core::Renderable;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{ParseTag, TagReflection, TagTokenIter};

#[derive(Copy, Clone, Debug, Default)]
pub struct IncrementTag;

impl IncrementTag {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TagReflection for IncrementTag {
    fn tag(&self) -> &'static str {
        "increment"
    }

    fn description(&self) -> &'static str {
        ""
    }
}

impl ParseTag for IncrementTag {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        _options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        let id = arguments
            .expect_next("Identifier expected.")?
            .expect_identifier()
            .into_result()?
            .to_string()
            .into();

        // no more arguments should be supplied, trying to supply them is an error
        arguments.expect_nothing()?;

        Ok(Box::new(Increment { id }))
    }

    fn reflection(&self) -> &dyn TagReflection {
        self
    }
}

#[derive(Clone, Debug)]
struct Increment {
    id: kstring::KString,
}

impl Renderable for Increment {
    fn render_to(&self, writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        let mut val = runtime
            .get_index(&self.id)
            .and_then(|i| i.as_scalar().and_then(|i| i.to_integer()))
            .unwrap_or(0);

        write!(writer, "{}", val).replace("Failed to render")?;
        val += 1;
        runtime.set_index(self.id.clone(), Value::scalar(val));
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct DecrementTag;

impl DecrementTag {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TagReflection for DecrementTag {
    fn tag(&self) -> &'static str {
        "decrement"
    }

    fn description(&self) -> &'static str {
        ""
    }
}

impl ParseTag for DecrementTag {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        _options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        let id = arguments
            .expect_next("Identifier expected.")?
            .expect_identifier()
            .into_result()?
            .to_string()
            .into();

        // no more arguments should be supplied, trying to supply them is an error
        arguments.expect_nothing()?;

        Ok(Box::new(Decrement { id }))
    }

    fn reflection(&self) -> &dyn TagReflection {
        self
    }
}

#[derive(Clone, Debug)]
struct Decrement {
    id: kstring::KString,
}

impl Renderable for Decrement {
    fn render_to(&self, writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        let mut val = runtime
            .get_index(&self.id)
            .and_then(|i| i.as_scalar().and_then(|i| i.to_integer()))
            .unwrap_or(0);

        val -= 1;
        write!(writer, "{}", val).replace("Failed to render")?;
        runtime.set_index(self.id.clone(), Value::scalar(val));
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use liquid_core::parser;
    use liquid_core::runtime;
    use liquid_core::runtime::RuntimeBuilder;

    use crate::stdlib;

    fn options() -> Language {
        let mut options = Language::default();
        options
            .tags
            .register("assign".to_string(), stdlib::AssignTag.into());
        options
            .tags
            .register("increment".to_string(), IncrementTag.into());
        options
            .tags
            .register("decrement".to_string(), DecrementTag.into());
        options
    }

    #[test]
    fn increment() {
        let text = "{% increment val %}{{ val }}";
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn decrement() {
        let text = "{% decrement val %}{{ val }}";
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "-1-1");
    }

    #[test]
    fn increment_and_decrement() {
        let text = "{% increment val %}{% increment val %}{% decrement val %}{% decrement val %}";
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "0110");
    }

    #[test]
    fn assign_and_increment() {
        let text = "{%- assign val = 9 -%}{% increment val %}{% increment val %}{{ val }}";
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "019");
    }
}
