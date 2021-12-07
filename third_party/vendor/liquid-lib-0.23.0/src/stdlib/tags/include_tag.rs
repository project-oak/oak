use std::io::Write;

use kstring::KString;
use liquid_core::error::ResultLiquidExt;
use liquid_core::Expression;
use liquid_core::Language;
use liquid_core::Renderable;
use liquid_core::ValueView;
use liquid_core::{runtime::StackFrame, Runtime};
use liquid_core::{Error, Result};
use liquid_core::{ParseTag, TagReflection, TagTokenIter};

#[derive(Copy, Clone, Debug, Default)]
pub struct IncludeTag;

impl IncludeTag {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TagReflection for IncludeTag {
    fn tag(&self) -> &'static str {
        "include"
    }

    fn description(&self) -> &'static str {
        ""
    }
}

impl ParseTag for IncludeTag {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        _options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        let partial = arguments.expect_next("Identifier or literal expected.")?;

        let partial = partial.expect_value().into_result()?;

        let mut vars: Vec<(KString, Expression)> = Vec::new();
        while let Ok(next) = arguments.expect_next("") {
            let id = next.expect_identifier().into_result()?.to_string();

            arguments
                .expect_next("\":\" expected.")?
                .expect_str(":")
                .into_result_custom_msg("expected \":\" to be used for the assignment")?;

            vars.push((
                id.into(),
                arguments
                    .expect_next("expected value")?
                    .expect_value()
                    .into_result()?,
            ));

            if let Ok(comma) = arguments.expect_next("") {
                // stop looking for variables if there is no comma
                // currently allows for one trailing comma
                if comma.expect_str(",").into_result().is_err() {
                    break;
                }
            }
        }

        arguments.expect_nothing()?;

        Ok(Box::new(Include { partial, vars }))
    }

    fn reflection(&self) -> &dyn TagReflection {
        self
    }
}

#[derive(Debug)]
struct Include {
    partial: Expression,
    vars: Vec<(KString, Expression)>,
}

impl Renderable for Include {
    fn render_to(&self, writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        let value = self.partial.evaluate(runtime)?;
        if !value.is_scalar() {
            return Error::with_msg("Can only `include` strings")
                .context("partial", format!("{}", value.source()))
                .into_err();
        }
        let name = value.to_kstr().into_owned();

        {
            // if there our additional variables creates a include object to access all the variables
            // from e.g. { include 'image.html' path="foo.png" }
            // then in image.html you could have <img src="{{include.path}}" />
            let mut pass_through = std::collections::HashMap::new();
            if !self.vars.is_empty() {
                for (id, val) in &self.vars {
                    let value = val
                        .try_evaluate(runtime)
                        .ok_or_else(|| Error::with_msg("failed to evaluate value"))?;

                    pass_through.insert(id.as_ref(), value);
                }
            }

            let scope = StackFrame::new(runtime, &pass_through);
            let partial = scope
                .partials()
                .get(&name)
                .trace_with(|| format!("{{% include {} %}}", self.partial).into())?;

            partial
                .render_to(writer, &scope)
                .trace_with(|| format!("{{% include {} %}}", self.partial).into())
                .context_key_with(|| self.partial.to_string().into())
                .value_with(|| name.to_string().into())?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::borrow;

    use liquid_core::parser;
    use liquid_core::partials;
    use liquid_core::partials::PartialCompiler;
    use liquid_core::runtime;
    use liquid_core::runtime::RuntimeBuilder;
    use liquid_core::Value;
    use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};

    use crate::stdlib;

    use super::*;

    #[derive(Default, Debug, Clone, Copy)]
    struct TestSource;

    impl partials::PartialSource for TestSource {
        fn contains(&self, _name: &str) -> bool {
            true
        }

        fn names(&self) -> Vec<&str> {
            vec![]
        }

        fn try_get<'a>(&'a self, name: &str) -> Option<borrow::Cow<'a, str>> {
            match name {
                "example.txt" => Some(r#"{{'whooo' | size}}{%comment%}What happens{%endcomment%} {%if num < numTwo%}wat{%else%}wot{%endif%} {%if num > numTwo%}wat{%else%}wot{%endif%}"#.into()),
                "example_var.txt" => Some(r#"{{example_var}}"#.into()),
                "example_multi_var.txt" => Some(r#"{{example_var}} {{example}}"#.into()),
                _ => None
            }
        }
    }

    fn options() -> Language {
        let mut options = Language::default();
        options
            .tags
            .register("include".to_string(), IncludeTag.into());
        options
            .blocks
            .register("comment".to_string(), stdlib::CommentBlock.into());
        options
            .blocks
            .register("if".to_string(), stdlib::IfBlock.into());
        options
    }

    #[derive(Clone, ParseFilter, FilterReflection)]
    #[filter(name = "size", description = "tests helper", parsed(SizeFilter))]
    pub struct SizeFilterParser;

    #[derive(Debug, Default, Display_filter)]
    #[name = "size"]
    pub struct SizeFilter;

    impl Filter for SizeFilter {
        fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
            if let Some(x) = input.as_scalar() {
                Ok(Value::scalar(x.to_kstr().len() as i64))
            } else if let Some(x) = input.as_array() {
                Ok(Value::scalar(x.size()))
            } else if let Some(x) = input.as_object() {
                Ok(Value::scalar(x.size()))
            } else {
                Ok(Value::scalar(0i64))
            }
        }
    }

    #[test]
    fn include_tag_quotes() {
        let text = "{% include 'example.txt' %}";
        let mut options = options();
        options
            .filters
            .register("size".to_string(), Box::new(SizeFilterParser));
        let template = parser::parse(text, &options)
            .map(runtime::Template::new)
            .unwrap();

        let partials = partials::OnDemandCompiler::<TestSource>::empty()
            .compile(::std::sync::Arc::new(options))
            .unwrap();
        let runtime = RuntimeBuilder::new()
            .set_partials(partials.as_ref())
            .build();
        runtime.set_global("num".into(), Value::scalar(5f64));
        runtime.set_global("numTwo".into(), Value::scalar(10f64));
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "5 wat wot");
    }

    #[test]
    fn include_variable() {
        let text = "{% include 'example_var.txt' example_var:\"hello\" %}";
        let options = options();
        let template = parser::parse(text, &options)
            .map(runtime::Template::new)
            .unwrap();

        let partials = partials::OnDemandCompiler::<TestSource>::empty()
            .compile(::std::sync::Arc::new(options))
            .unwrap();
        let runtime = RuntimeBuilder::new()
            .set_partials(partials.as_ref())
            .build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "hello");
    }

    #[test]
    fn include_multiple_variables() {
        let text = "{% include 'example_multi_var.txt' example_var:\"hello\", example:\"world\" %}";
        let options = options();
        let template = parser::parse(text, &options)
            .map(runtime::Template::new)
            .unwrap();

        let partials = partials::OnDemandCompiler::<TestSource>::empty()
            .compile(::std::sync::Arc::new(options))
            .unwrap();
        let runtime = RuntimeBuilder::new()
            .set_partials(partials.as_ref())
            .build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "hello world");
    }

    #[test]
    fn include_multiple_variables_trailing_commma() {
        let text = "{% include 'example_multi_var.txt' example_var:\"hello\", example:\"dogs\", %}";
        let options = options();
        let template = parser::parse(text, &options)
            .map(runtime::Template::new)
            .unwrap();

        let partials = partials::OnDemandCompiler::<TestSource>::empty()
            .compile(::std::sync::Arc::new(options))
            .unwrap();
        let runtime = RuntimeBuilder::new()
            .set_partials(partials.as_ref())
            .build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "hello dogs");
    }

    #[test]
    fn no_file() {
        let text = "{% include 'file_does_not_exist.liquid' %}";
        let mut options = options();
        options
            .filters
            .register("size".to_string(), Box::new(SizeFilterParser));
        let template = parser::parse(text, &options)
            .map(runtime::Template::new)
            .unwrap();

        let partials = partials::OnDemandCompiler::<TestSource>::empty()
            .compile(::std::sync::Arc::new(options))
            .unwrap();
        let runtime = RuntimeBuilder::new()
            .set_partials(partials.as_ref())
            .build();
        runtime.set_global("num".into(), Value::scalar(5f64));
        runtime.set_global("numTwo".into(), Value::scalar(10f64));
        let output = template.render(&runtime);
        assert!(output.is_err());
    }
}
