use std::io::Write;

use liquid_core::runtime::{Interrupt, InterruptRegister};
use liquid_core::Language;
use liquid_core::Renderable;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{ParseTag, TagReflection, TagTokenIter};

#[derive(Copy, Clone, Debug, Default)]
pub struct BreakTag;

impl BreakTag {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TagReflection for BreakTag {
    fn tag(&self) -> &'static str {
        "break"
    }

    fn description(&self) -> &'static str {
        ""
    }
}

impl ParseTag for BreakTag {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        _options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        // no arguments should be supplied, trying to supply them is an error
        arguments.expect_nothing()?;
        Ok(Box::new(Break))
    }

    fn reflection(&self) -> &dyn TagReflection {
        self
    }
}

#[derive(Copy, Clone, Debug)]
struct Break;

impl Renderable for Break {
    fn render_to(&self, _writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        runtime
            .registers()
            .get_mut::<InterruptRegister>()
            .set(Interrupt::Break);
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct ContinueTag;

impl ContinueTag {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TagReflection for ContinueTag {
    fn tag(&self) -> &'static str {
        "continue"
    }

    fn description(&self) -> &'static str {
        ""
    }
}

impl ParseTag for ContinueTag {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        _options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        // no arguments should be supplied, trying to supply them is an error
        arguments.expect_nothing()?;
        Ok(Box::new(Continue))
    }

    fn reflection(&self) -> &dyn TagReflection {
        self
    }
}

#[derive(Copy, Clone, Debug)]
struct Continue;

impl Renderable for Continue {
    fn render_to(&self, _writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        runtime
            .registers()
            .get_mut::<InterruptRegister>()
            .set(Interrupt::Continue);
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
        options.tags.register("break".to_string(), BreakTag.into());
        options
            .tags
            .register("continue".to_string(), ContinueTag.into());
        options
            .blocks
            .register("for".to_string(), stdlib::ForBlock.into());
        options
            .blocks
            .register("if".to_string(), stdlib::IfBlock.into());
        options
    }

    #[test]
    fn test_simple_break() {
        let text = concat!(
            "{% for i in (0..10) %}",
            "enter-{{i}};",
            "{% if i == 2 %}break-{{i}}\n{% break %}{% endif %}",
            "exit-{{i}}\n",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let rt = RuntimeBuilder::new().build();
        let output = template.render(&rt).unwrap();
        assert_eq!(
            output,
            concat!("enter-0;exit-0\n", "enter-1;exit-1\n", "enter-2;break-2\n")
        );
    }

    #[test]
    fn test_nested_break() {
        // assert that a {% break %} only breaks out of the innermost loop
        let text = concat!(
            "{% for outer in (0..3) %}",
            "enter-{{outer}}; ",
            "{% for inner in (6..10) %}",
            "{% if inner == 8 %}break, {% break %}{% endif %}",
            "{{ inner }}, ",
            "{% endfor %}",
            "exit-{{outer}}\n",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let rt = RuntimeBuilder::new().build();
        let output = template.render(&rt).unwrap();
        assert_eq!(
            output,
            concat!(
                "enter-0; 6, 7, break, exit-0\n",
                "enter-1; 6, 7, break, exit-1\n",
                "enter-2; 6, 7, break, exit-2\n",
                "enter-3; 6, 7, break, exit-3\n",
            )
        );
    }

    #[test]
    fn test_simple_continue() {
        let text = concat!(
            "{% for i in (0..5) %}",
            "enter-{{i}};",
            "{% if i == 2 %}continue-{{i}}\n{% continue %}{% endif %}",
            "exit-{{i}}\n",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let rt = RuntimeBuilder::new().build();
        let output = template.render(&rt).unwrap();
        assert_eq!(
            output,
            concat!(
                "enter-0;exit-0\n",
                "enter-1;exit-1\n",
                "enter-2;continue-2\n",
                "enter-3;exit-3\n",
                "enter-4;exit-4\n",
                "enter-5;exit-5\n",
            )
        );
    }

    #[test]
    fn test_nested_continue() {
        // assert that a {% continue %} only jumps out of the innermost loop
        let text = concat!(
            "{% for outer in (0..3) %}",
            "enter-{{outer}}; ",
            "{% for inner in (6..10) %}",
            "{% if inner == 8 %}continue, {% continue %}{% endif %}",
            "{{ inner }}, ",
            "{% endfor %}",
            "exit-{{outer}}\n",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let rt = RuntimeBuilder::new().build();
        let output = template.render(&rt).unwrap();
        assert_eq!(
            output,
            concat!(
                "enter-0; 6, 7, continue, 9, 10, exit-0\n",
                "enter-1; 6, 7, continue, 9, 10, exit-1\n",
                "enter-2; 6, 7, continue, 9, 10, exit-2\n",
                "enter-3; 6, 7, continue, 9, 10, exit-3\n",
            )
        );
    }
}
