use std::collections::HashMap;
use std::io::Write;

use liquid_core::error::{ResultLiquidExt, ResultLiquidReplaceExt};
use liquid_core::parser::TagToken;
use liquid_core::parser::TryMatchToken;
use liquid_core::Expression;
use liquid_core::Language;
use liquid_core::Renderable;
use liquid_core::Runtime;
use liquid_core::ValueView;
use liquid_core::{Error, Result};
use liquid_core::{ParseTag, TagReflection, TagTokenIter};

#[derive(Copy, Clone, Debug, Default)]
pub struct CycleTag;

impl CycleTag {
    pub fn new() -> Self {
        Self::default()
    }
}

impl TagReflection for CycleTag {
    fn tag(&self) -> &'static str {
        "cycle"
    }

    fn description(&self) -> &'static str {
        ""
    }
}

impl ParseTag for CycleTag {
    fn parse(
        &self,
        arguments: TagTokenIter<'_>,
        options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        parse_cycle(arguments, options).map(|opt| Box::new(opt) as Box<dyn Renderable>)
    }

    fn reflection(&self) -> &dyn TagReflection {
        self
    }
}

/// Internal implementation of cycle, to allow easier testing.
fn parse_cycle(mut arguments: TagTokenIter<'_>, _options: &Language) -> Result<Cycle> {
    let mut name = String::new();
    let mut values = Vec::new();

    let first = arguments.expect_next("Identifier or value expected")?;
    let second = arguments.next();
    match second.as_ref().map(TagToken::as_str) {
        Some(":") => {
            name = match first.expect_identifier() {
                TryMatchToken::Matches(name) => name.to_string(),
                TryMatchToken::Fails(name) => match name.expect_literal() {
                    // This will allow non string literals such as 0 to be parsed as such.
                    // Is this ok or should more specific functions be created?
                    TryMatchToken::Matches(name) => name.to_kstr().into_string(),
                    TryMatchToken::Fails(name) => return name.raise_error().into_err(),
                },
            };
        }
        Some(",") | None => {
            // first argument is the first item in the cycle
            values.push(first.expect_value().into_result()?);
        }
        Some(_) => {
            return second
                .expect("is some")
                .raise_custom_error("\":\" or \",\" expected.")
                .into_err();
        }
    }

    loop {
        match arguments.next() {
            Some(a) => {
                values.push(a.expect_value().into_result()?);
            }
            None => break,
        }
        let next = arguments.next();
        match next.as_ref().map(TagToken::as_str) {
            Some(",") => {}
            None => break,
            Some(_) => {
                return next
                    .expect("is some")
                    .raise_custom_error("\",\" expected.")
                    .into_err();
            }
        }
    }

    if name.is_empty() {
        name = itertools::join(values.iter(), "-");
    }

    // no more arguments should be supplied, trying to supply them is an error
    arguments.expect_nothing()?;

    Ok(Cycle { name, values })
}

#[derive(Clone, Debug)]
struct Cycle {
    name: String,
    values: Vec<Expression>,
}

impl Cycle {
    fn trace(&self) -> String {
        format!(
            "{{% cycle {} %}}",
            itertools::join(self.values.iter(), ", ")
        )
    }
}

impl Renderable for Cycle {
    fn render_to(&self, writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        let expr = runtime
            .registers()
            .get_mut::<CycleRegister>()
            .cycle(&self.name, &self.values)
            .trace_with(|| self.trace().into())?;
        let value = expr.evaluate(runtime).trace_with(|| self.trace().into())?;
        write!(writer, "{}", value.render()).replace("Failed to render")?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct CycleRegister {
    // The indices of all the cycles encountered during rendering.
    cycles: HashMap<String, usize>,
}

impl CycleRegister {
    fn cycle<'e>(&mut self, name: &str, values: &'e [Expression]) -> Result<&'e Expression> {
        let index = self.cycle_index(name, values.len());
        if index >= values.len() {
            return Error::with_msg(
                "cycle index out of bounds, most likely from mismatched cycles",
            )
            .context("index", format!("{}", index))
            .context("count", format!("{}", values.len()))
            .into_err();
        }

        Ok(&values[index])
    }

    fn cycle_index(&mut self, name: &str, max: usize) -> usize {
        let i = self.cycles.entry(name.to_owned()).or_insert(0);
        let j = *i;
        *i = (*i + 1) % max;
        j
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use liquid_core::model::Value;
    use liquid_core::parser;
    use liquid_core::runtime;
    use liquid_core::runtime::RuntimeBuilder;

    fn options() -> Language {
        let mut options = Language::default();
        options.tags.register("cycle".to_string(), CycleTag.into());
        options
    }

    #[test]
    fn unnamed_cycle_gets_a_name() {
        let tag = parser::Tag::new("{% cycle this, cycle, has, no, name %}").unwrap();
        let cycle = parse_cycle(tag.into_tokens(), &options()).unwrap();
        assert!(!cycle.name.is_empty());
    }

    #[test]
    fn named_values_are_independent() {
        let text = concat!(
            "{% cycle 'a': 'one', 'two', 'three' %}\n",
            "{% cycle 'a': 'one', 'two', 'three' %}\n",
            "{% cycle 'b': 'one', 'two', 'three' %}\n",
            "{% cycle 'b': 'one', 'two', 'three' %}\n"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime);

        assert_eq!(output.unwrap(), "one\ntwo\none\ntwo\n");
    }

    #[test]
    fn values_are_cycled() {
        let text = concat!(
            "{% cycle 'one', 'two', 'three' %}\n",
            "{% cycle 'one', 'two', 'three' %}\n",
            "{% cycle 'one', 'two', 'three' %}\n",
            "{% cycle 'one', 'two', 'three' %}\n"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime);

        assert_eq!(output.unwrap(), "one\ntwo\nthree\none\n");
    }

    #[test]
    fn values_can_be_variables() {
        let text = concat!(
            "{% cycle alpha, beta, gamma %}\n",
            "{% cycle alpha, beta, gamma %}\n",
            "{% cycle alpha, beta, gamma %}\n",
            "{% cycle alpha, beta, gamma %}\n"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global("alpha".into(), Value::scalar(1f64));
        runtime.set_global("beta".into(), Value::scalar(2f64));
        runtime.set_global("gamma".into(), Value::scalar(3f64));

        let output = template.render(&runtime);

        assert_eq!(output.unwrap(), "1\n2\n3\n1\n");
    }

    #[test]
    fn bad_cycle_indices_dont_crash() {
        // note the pair of cycle tags with the same name but a differing
        // number of elements
        let text = concat!("{% cycle c: 1, 2 %}\n", "{% cycle c: 1 %}\n");

        let runtime = RuntimeBuilder::new().build();
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();
        let output = template.render(&runtime);
        assert!(output.is_err());
    }
}
