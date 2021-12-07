use std::fmt;
use std::io::Write;

use liquid_core::error::{ResultLiquidExt, ResultLiquidReplaceExt};
use liquid_core::model::{Object, ObjectView, Value, ValueCow, ValueView};
use liquid_core::parser::BlockElement;
use liquid_core::parser::TryMatchToken;
use liquid_core::runtime::{Interrupt, InterruptRegister};
use liquid_core::Expression;
use liquid_core::Language;
use liquid_core::Renderable;
use liquid_core::Template;
use liquid_core::{runtime::StackFrame, Runtime};
use liquid_core::{BlockReflection, ParseBlock, TagBlock, TagTokenIter};
use liquid_core::{Error, Result};

#[derive(Copy, Clone, Debug, Default)]
pub struct ForBlock;

impl ForBlock {
    pub fn new() -> Self {
        Self::default()
    }
}

impl BlockReflection for ForBlock {
    fn start_tag(&self) -> &str {
        "for"
    }

    fn end_tag(&self) -> &str {
        "endfor"
    }

    fn description(&self) -> &str {
        ""
    }
}

impl ParseBlock for ForBlock {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        mut tokens: TagBlock<'_, '_>,
        options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        let var_name = arguments
            .expect_next("Identifier expected.")?
            .expect_identifier()
            .into_result()?;

        arguments
            .expect_next("\"in\" expected.")?
            .expect_str("in")
            .into_result_custom_msg("\"in\" expected.")?;

        let range = arguments.expect_next("Array or range expected.")?;
        let range = match range.expect_value() {
            TryMatchToken::Matches(array) => RangeExpression::Array(array),
            TryMatchToken::Fails(range) => match range.expect_range() {
                TryMatchToken::Matches((start, stop)) => RangeExpression::Counted(start, stop),
                TryMatchToken::Fails(range) => return range.raise_error().into_err(),
            },
        };

        // now we get to check for parameters...
        let mut limit = None;
        let mut offset = None;
        let mut reversed = false;

        while let Some(token) = arguments.next() {
            match token.as_str() {
                "limit" => limit = Some(parse_attr(&mut arguments)?),
                "offset" => offset = Some(parse_attr(&mut arguments)?),
                "reversed" => reversed = true,
                _ => {
                    return token
                        .raise_custom_error("\"limit\", \"offset\" or \"reversed\" expected.")
                        .into_err();
                }
            }
        }

        // no more arguments should be supplied, trying to supply them is an error
        arguments.expect_nothing()?;

        let mut item_template = Vec::new();
        let mut else_template = None;

        while let Some(element) = tokens.next()? {
            match element {
                BlockElement::Tag(mut tag) => match tag.name() {
                    "else" => {
                        // no more arguments should be supplied, trying to supply them is an error
                        tag.tokens().expect_nothing()?;
                        else_template = Some(tokens.parse_all(options)?);
                        break;
                    }
                    _ => item_template.push(tag.parse(&mut tokens, options)?),
                },
                element => item_template.push(element.parse(&mut tokens, options)?),
            }
        }

        let item_template = Template::new(item_template);
        let else_template = else_template.map(Template::new);

        tokens.assert_empty();
        Ok(Box::new(For {
            var_name: kstring::KString::from_ref(var_name),
            range,
            item_template,
            else_template,
            limit,
            offset,
            reversed,
        }))
    }

    fn reflection(&self) -> &dyn BlockReflection {
        self
    }
}

#[derive(Debug)]
struct For {
    var_name: kstring::KString,
    range: RangeExpression,
    item_template: Template,
    else_template: Option<Template>,
    limit: Option<Expression>,
    offset: Option<Expression>,
    reversed: bool,
}

impl For {
    fn trace(&self) -> String {
        trace_for_tag(
            self.var_name.as_str(),
            &self.range,
            &self.limit,
            &self.offset,
            self.reversed,
        )
    }
}

fn trace_for_tag(
    var_name: &str,
    range: &RangeExpression,
    limit: &Option<Expression>,
    offset: &Option<Expression>,
    reversed: bool,
) -> String {
    let mut parameters = vec![];
    if let Some(limit) = limit {
        parameters.push(format!("limit:{}", limit));
    }
    if let Some(offset) = offset {
        parameters.push(format!("offset:{}", offset));
    }
    if reversed {
        parameters.push("reversed".to_owned());
    }
    format!(
        "{{% for {} in {} {} %}}",
        var_name,
        range,
        itertools::join(parameters.iter(), ", ")
    )
}

impl Renderable for For {
    fn render_to(&self, writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        let range = self
            .range
            .evaluate(runtime)
            .trace_with(|| self.trace().into())?;
        let array = range.evaluate()?;
        let limit = evaluate_attr(&self.limit, runtime)?;
        let offset = evaluate_attr(&self.offset, runtime)?.unwrap_or(0);
        let array = iter_array(array, limit, offset, self.reversed);

        match array.len() {
            0 => {
                if let Some(ref t) = self.else_template {
                    t.render_to(writer, runtime)
                        .trace("{{% else %}}")
                        .trace_with(|| self.trace().into())?;
                }
            }

            range_len => {
                let parentloop = runtime.try_get(&[liquid_core::model::Scalar::new("forloop")]);
                let parentloop_ref = parentloop.as_ref().map(|v| v.as_view());
                for (i, v) in array.into_iter().enumerate() {
                    let forloop = ForloopObject::new(i, range_len).parentloop(parentloop_ref);
                    let mut root =
                        std::collections::HashMap::<kstring::KStringRef<'_>, &dyn ValueView>::new();
                    root.insert("forloop".into(), &forloop);
                    root.insert(self.var_name.as_ref(), &v);

                    let scope = StackFrame::new(runtime, &root);
                    self.item_template
                        .render_to(writer, &scope)
                        .trace_with(|| self.trace().into())
                        .context_key("index")
                        .value_with(|| format!("{}", i + 1).into())?;

                    // given that we're at the end of the loop body
                    // already, dealing with a `continue` signal is just
                    // clearing the interrupt and carrying on as normal. A
                    // `break` requires some special handling, though.
                    let current_interrupt =
                        scope.registers().get_mut::<InterruptRegister>().reset();
                    if let Some(Interrupt::Break) = current_interrupt {
                        break;
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, ValueView, ObjectView)]
struct ForloopObject<'p> {
    length: i64,
    parentloop: Option<&'p dyn ValueView>,
    index0: i64,
    index: i64,
    rindex0: i64,
    rindex: i64,
    first: bool,
    last: bool,
}

impl<'p> ForloopObject<'p> {
    fn new(i: usize, len: usize) -> Self {
        let i = i as i64;
        let len = len as i64;
        let first = i == 0;
        let last = i == (len - 1);
        Self {
            length: len,
            parentloop: None,
            index0: i,
            index: i + 1,
            rindex0: len - i - 1,
            rindex: len - i,
            first,
            last,
        }
    }

    fn parentloop(mut self, parentloop: Option<&'p dyn ValueView>) -> Self {
        self.parentloop = parentloop;
        self
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct TableRowBlock;

impl TableRowBlock {
    pub fn new() -> Self {
        Self::default()
    }
}

impl BlockReflection for TableRowBlock {
    fn start_tag(&self) -> &str {
        "tablerow"
    }

    fn end_tag(&self) -> &str {
        "endtablerow"
    }

    fn description(&self) -> &str {
        ""
    }
}

impl ParseBlock for TableRowBlock {
    fn parse(
        &self,
        mut arguments: TagTokenIter<'_>,
        mut tokens: TagBlock<'_, '_>,
        options: &Language,
    ) -> Result<Box<dyn Renderable>> {
        let var_name = arguments
            .expect_next("Identifier expected.")?
            .expect_identifier()
            .into_result()?;

        arguments
            .expect_next("\"in\" expected.")?
            .expect_str("in")
            .into_result_custom_msg("\"in\" expected.")?;

        let range = arguments.expect_next("Array or range expected.")?;
        let range = match range.expect_value() {
            TryMatchToken::Matches(array) => RangeExpression::Array(array),
            TryMatchToken::Fails(range) => match range.expect_range() {
                TryMatchToken::Matches((start, stop)) => RangeExpression::Counted(start, stop),
                TryMatchToken::Fails(range) => return range.raise_error().into_err(),
            },
        };

        // now we get to check for parameters...
        let mut cols = None;
        let mut limit = None;
        let mut offset = None;

        while let Some(token) = arguments.next() {
            match token.as_str() {
                "cols" => cols = Some(parse_attr(&mut arguments)?),
                "limit" => limit = Some(parse_attr(&mut arguments)?),
                "offset" => offset = Some(parse_attr(&mut arguments)?),
                _ => {
                    return token
                        .raise_custom_error("\"cols\", \"limit\" or \"offset\" expected.")
                        .into_err();
                }
            }
        }

        // no more arguments should be supplied, trying to supply them is an error
        arguments.expect_nothing()?;

        let item_template = Template::new(tokens.parse_all(options)?);

        tokens.assert_empty();
        Ok(Box::new(TableRow {
            var_name: kstring::KString::from_ref(var_name),
            range,
            item_template,
            cols,
            limit,
            offset,
        }))
    }

    fn reflection(&self) -> &dyn BlockReflection {
        self
    }
}

#[derive(Debug)]
struct TableRow {
    var_name: kstring::KString,
    range: RangeExpression,
    item_template: Template,
    cols: Option<Expression>,
    limit: Option<Expression>,
    offset: Option<Expression>,
}

impl TableRow {
    fn trace(&self) -> String {
        trace_tablerow_tag(
            self.var_name.as_str(),
            &self.range,
            &self.cols,
            &self.limit,
            &self.offset,
        )
    }
}

fn trace_tablerow_tag(
    var_name: &str,
    range: &RangeExpression,
    cols: &Option<Expression>,
    limit: &Option<Expression>,
    offset: &Option<Expression>,
) -> String {
    let mut parameters = vec![];
    if let Some(cols) = cols {
        parameters.push(format!("cols:{}", cols));
    }
    if let Some(limit) = limit {
        parameters.push(format!("limit:{}", limit));
    }
    if let Some(offset) = offset {
        parameters.push(format!("offset:{}", offset));
    }
    format!(
        "{{% for {} in {} {} %}}",
        var_name,
        range,
        itertools::join(parameters.iter(), ", ")
    )
}

impl Renderable for TableRow {
    fn render_to(&self, writer: &mut dyn Write, runtime: &dyn Runtime) -> Result<()> {
        let range = self
            .range
            .evaluate(runtime)
            .trace_with(|| self.trace().into())?;
        let array = range.evaluate()?;
        let cols = evaluate_attr(&self.cols, runtime)?;
        let limit = evaluate_attr(&self.limit, runtime)?;
        let offset = evaluate_attr(&self.offset, runtime)?.unwrap_or(0);
        let array = iter_array(array, limit, offset, false);

        let mut helper_vars = Object::new();

        let range_len = array.len();
        helper_vars.insert("length".into(), Value::scalar(range_len as i64));

        for (i, v) in array.into_iter().enumerate() {
            let cols = cols.unwrap_or(range_len);
            let col_index = i % cols;
            let row_index = i / cols;

            let tablerow = TableRowObject::new(i, range_len, col_index, cols);
            let mut root =
                std::collections::HashMap::<kstring::KStringRef<'_>, &dyn ValueView>::new();
            root.insert("tablerow".into(), &tablerow);
            root.insert(self.var_name.as_ref(), &v);

            if tablerow.col_first {
                write!(writer, "<tr class=\"row{}\">", row_index + 1)
                    .replace("Failed to render")?;
            }
            write!(writer, "<td class=\"col{}\">", col_index + 1).replace("Failed to render")?;

            let scope = StackFrame::new(runtime, &root);
            self.item_template
                .render_to(writer, &scope)
                .trace_with(|| self.trace().into())
                .context_key("index")
                .value_with(|| format!("{}", i + 1).into())?;

            write!(writer, "</td>").replace("Failed to render")?;
            if tablerow.col_last {
                write!(writer, "</tr>").replace("Failed to render")?;
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, ValueView, ObjectView)]
struct TableRowObject {
    length: i64,
    index0: i64,
    index: i64,
    rindex0: i64,
    rindex: i64,
    first: bool,
    last: bool,
    col0: i64,
    col: i64,
    col_first: bool,
    col_last: bool,
}

impl TableRowObject {
    fn new(i: usize, len: usize, col: usize, cols: usize) -> Self {
        let i = i as i64;
        let len = len as i64;
        let col = col as i64;
        let cols = cols as i64;
        let first = i == 0;
        let last = i == (len - 1);
        let col_first = col == 0;
        let col_last = col == (cols - 1) || last;
        Self {
            length: len,
            index0: i,
            index: i + 1,
            rindex0: len - i - 1,
            rindex: len - i,
            first,
            last,
            col0: col,
            col: (col + 1),
            col_first,
            col_last,
        }
    }
}

/// Extracts an integer value or an identifier from the token stream
fn parse_attr(arguments: &mut TagTokenIter<'_>) -> Result<Expression> {
    arguments
        .expect_next("\":\" expected.")?
        .expect_str(":")
        .into_result_custom_msg("\":\" expected.")?;

    arguments
        .expect_next("Value expected.")?
        .expect_value()
        .into_result()
}

/// Evaluates an attribute, returning Ok(None) if input is also None.
fn evaluate_attr(attr: &Option<Expression>, runtime: &dyn Runtime) -> Result<Option<usize>> {
    match attr {
        Some(attr) => {
            let value = attr.evaluate(runtime)?;
            let value = value
                .as_scalar()
                .and_then(|s| s.to_integer())
                .ok_or_else(|| unexpected_value_error("whole number", Some(value.type_name())))?
                as usize;
            Ok(Some(value))
        }
        None => Ok(None),
    }
}

#[derive(Clone, Debug)]
enum RangeExpression {
    Array(Expression),
    Counted(Expression, Expression),
}

impl RangeExpression {
    pub fn evaluate<'r>(&'r self, runtime: &'r dyn Runtime) -> Result<Range<'r>> {
        let range = match *self {
            RangeExpression::Array(ref array_id) => {
                let array = array_id.evaluate(runtime)?;
                Range::Array(array)
            }

            RangeExpression::Counted(ref start_arg, ref stop_arg) => {
                let start = int_argument(start_arg, runtime, "start")? as i64;
                let stop = int_argument(stop_arg, runtime, "end")? as i64;
                Range::Counted(start, stop)
            }
        };

        Ok(range)
    }
}

impl fmt::Display for RangeExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            RangeExpression::Array(ref arr) => write!(f, "{}", arr),
            RangeExpression::Counted(ref start, ref end) => write!(f, "({}..{})", start, end),
        }
    }
}

#[derive(Clone, Debug)]
enum Range<'r> {
    Array(ValueCow<'r>),
    Counted(i64, i64),
}

impl<'r> Range<'r> {
    pub fn evaluate<'s>(&'s self) -> Result<Vec<ValueCow<'s>>> {
        let range = match self {
            Range::Array(array) => get_array(array.as_view())?,

            Range::Counted(start, stop) => {
                let range = (*start)..=(*stop);
                range.map(|x| Value::scalar(x).into()).collect()
            }
        };

        Ok(range)
    }
}

fn get_array(array: &dyn ValueView) -> Result<Vec<ValueCow<'_>>> {
    if let Some(x) = array.as_array() {
        Ok(x.values().map(|v| ValueCow::Borrowed(v)).collect())
    } else if let Some(x) = array.as_object() {
        let x = x
            .iter()
            .map(|(k, v)| {
                let k = k.into_owned();
                let arr = vec![Value::scalar(k), v.to_value()];
                Value::Array(arr).into()
            })
            .collect();
        Ok(x)
    } else if array.is_state() || array.is_nil() {
        Ok(vec![])
    } else {
        Err(unexpected_value_error("array", Some(array.type_name())))
    }
}

fn int_argument(arg: &Expression, runtime: &dyn Runtime, arg_name: &str) -> Result<isize> {
    let value = arg.evaluate(runtime)?;

    let value = value
        .as_scalar()
        .and_then(|v| v.to_integer())
        .ok_or_else(|| unexpected_value_error("whole number", Some(value.type_name())))
        .context_key_with(|| arg_name.to_owned().into())
        .value_with(|| value.to_kstr().into_owned())?;

    Ok(value as isize)
}

fn iter_array(
    mut range: Vec<ValueCow<'_>>,
    limit: Option<usize>,
    offset: usize,
    reversed: bool,
) -> Vec<ValueCow<'_>> {
    let offset = ::std::cmp::min(offset, range.len());
    let limit = limit
        .map(|l| ::std::cmp::min(l, range.len()))
        .unwrap_or_else(|| range.len() - offset);
    range.drain(0..offset);
    range.resize(limit, Value::Nil.into());

    if reversed {
        range.reverse();
    };

    range
}

/// Format an error for an unexpected value.
fn unexpected_value_error<S: ToString>(expected: &str, actual: Option<S>) -> Error {
    let actual = actual.map(|x| x.to_string());
    unexpected_value_error_string(expected, actual)
}

fn unexpected_value_error_string(expected: &str, actual: Option<String>) -> Error {
    let actual = actual.unwrap_or_else(|| "nothing".to_owned());
    Error::with_msg(format!("Expected {}, found `{}`", expected, actual))
}

#[cfg(test)]
mod test {
    use liquid_core::model::ValueView;
    use liquid_core::parser;
    use liquid_core::runtime;
    use liquid_core::runtime::RuntimeBuilder;
    use liquid_core::{Display_filter, Filter, FilterReflection, ParseFilter};

    use crate::stdlib;

    use super::*;

    fn options() -> Language {
        let mut options = Language::default();
        options.blocks.register("for".to_string(), ForBlock.into());
        options
            .blocks
            .register("tablerow".to_string(), TableRowBlock.into());
        options
            .tags
            .register("assign".to_string(), stdlib::AssignTag.into());
        options
    }

    #[test]
    fn loop_over_array() {
        let text = concat!("{% for name in array %}", "test {{name}} ", "{% endfor %}",);

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global(
            "array".into(),
            Value::Array(vec![
                Value::scalar(22f64),
                Value::scalar(23f64),
                Value::scalar(24f64),
                Value::scalar("wat".to_owned()),
            ]),
        );
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "test 22 test 23 test 24 test wat ");
    }

    #[test]
    fn loop_over_range_literals() {
        let text = concat!(
            "{% for name in (42..46) %}",
            "#{{forloop.index}} test {{name}} | ",
            "{% endfor %}",
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(
            output,
            "#1 test 42 | #2 test 43 | #3 test 44 | #4 test 45 | #5 test 46 | "
        );
    }

    #[test]
    fn loop_over_range_vars() {
        let text = concat!(
            "{% for x in (alpha .. omega) %}",
            "#{{forloop.index}} test {{x}}, ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global("alpha".into(), Value::scalar(42i64));
        runtime.set_global("omega".into(), Value::scalar(46i64));
        let output = template.render(&runtime).unwrap();
        assert_eq!(
            output,
            "#1 test 42, #2 test 43, #3 test 44, #4 test 45, #5 test 46, "
        );
    }

    #[test]
    fn nested_forloops() {
        // test that nest nested for loops work, and that the
        // variable scopes between the inner and outer variable
        // scopes do not overlap.
        let text = concat!(
            "{% for outer in (1..5) %}",
            ">>{{forloop.index0}}:{{outer}}>>",
            "{% for inner in (6..10) %}",
            "{{outer}}:{{forloop.index0}}:{{inner}},",
            "{% endfor %}",
            ">>{{outer}}>>\n",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(
            output,
            concat!(
                ">>0:1>>1:0:6,1:1:7,1:2:8,1:3:9,1:4:10,>>1>>\n",
                ">>1:2>>2:0:6,2:1:7,2:2:8,2:3:9,2:4:10,>>2>>\n",
                ">>2:3>>3:0:6,3:1:7,3:2:8,3:3:9,3:4:10,>>3>>\n",
                ">>3:4>>4:0:6,4:1:7,4:2:8,4:3:9,4:4:10,>>4>>\n",
                ">>4:5>>5:0:6,5:1:7,5:2:8,5:3:9,5:4:10,>>5>>\n",
            )
        );
    }

    #[test]
    fn nested_forloops_with_else() {
        // test that nested for loops parse their `else` blocks correctly
        let text = concat!(
            "{% for x in i %}",
            "{% for y in j %}inner{% else %}empty inner{% endfor %}",
            "{% else %}",
            "empty outer",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global("i".into(), Value::Array(vec![]));
        runtime.set_global("j".into(), Value::Array(vec![]));
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "empty outer");

        runtime.set_global("i".into(), Value::Array(vec![Value::scalar(1i64)]));
        runtime.set_global("j".into(), Value::Array(vec![]));
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "empty inner");
    }

    #[test]
    fn degenerate_range_is_safe() {
        // make sure that a degenerate range (i.e. where max < min)
        // doesn't result in an infinte loop
        let text = concat!("{% for x in (10 .. 0) %}", "{{x}}", "{% endfor %}");
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "");
    }

    #[test]
    fn limited_loop() {
        let text = concat!(
            "{% for i in (1..100) limit:2 %}",
            "{{ i }} ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "1 2 ");
    }

    #[test]
    fn offset_loop() {
        let text = concat!(
            "{% for i in (1..10) offset:4 %}",
            "{{ i }} ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "5 6 7 8 9 10 ");
    }

    #[test]
    fn offset_and_limited_loop() {
        let text = concat!(
            "{% for i in (1..10) offset:4 limit:2 %}",
            "{{ i }} ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "5 6 ");
    }

    #[test]
    fn reversed_loop() {
        let text = concat!(
            "{% for i in (1..10) reversed %}",
            "{{ i }} ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "10 9 8 7 6 5 4 3 2 1 ");
    }

    #[test]
    fn sliced_and_reversed_loop() {
        let text = concat!(
            "{% for i in (1..10) reversed offset:1 limit:5%}",
            "{{ i }} ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "6 5 4 3 2 ");
    }

    #[test]
    fn empty_loop_invokes_else_template() {
        let text = concat!(
            "{% for i in (1..10) limit:0 %}",
            "{{ i }} ",
            "{% else %}",
            "There are no items!",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "There are no items!");
    }

    #[test]
    fn nil_loop_invokes_else_template() {
        let text = concat!(
            "{% for i in nil %}",
            "{{ i }} ",
            "{% else %}",
            "There are no items!",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "There are no items!");
    }

    #[test]
    fn limit_greater_than_iterator_length() {
        let text = concat!("{% for i in (1..5) limit:10 %}", "{{ i }} ", "{% endfor %}");
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "1 2 3 4 5 ");
    }

    #[test]
    fn loop_variables() {
        let text = concat!(
            "{% for v in (100..102) %}",
            "length: {{forloop.length}}, ",
            "index: {{forloop.index}}, ",
            "index0: {{forloop.index0}}, ",
            "rindex: {{forloop.rindex}}, ",
            "rindex0: {{forloop.rindex0}}, ",
            "value: {{v}}, ",
            "first: {{forloop.first}}, ",
            "last: {{forloop.last}}\n",
            "{% endfor %}",
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(
                output,
                concat!(
    "length: 3, index: 1, index0: 0, rindex: 3, rindex0: 2, value: 100, first: true, last: false\n",
    "length: 3, index: 2, index0: 1, rindex: 2, rindex0: 1, value: 101, first: false, last: false\n",
    "length: 3, index: 3, index0: 2, rindex: 1, rindex0: 0, value: 102, first: false, last: true\n",
    )
            );
    }

    #[derive(Clone, ParseFilter, FilterReflection)]
    #[filter(name = "shout", description = "tests helper", parsed(ShoutFilter))]
    pub struct ShoutFilterParser;

    #[derive(Debug, Default, Display_filter)]
    #[name = "shout"]
    pub struct ShoutFilter;

    impl Filter for ShoutFilter {
        fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
            Ok(Value::scalar(input.to_kstr().to_uppercase()))
        }
    }

    #[test]
    fn use_filters() {
        let text = concat!(
            "{% for name in array %}",
            "test {{name | shout}} ",
            "{% endfor %}",
        );

        let mut options = options();
        options
            .filters
            .register("shout".to_string(), Box::new(ShoutFilterParser));
        let template = parser::parse(text, &options)
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();

        runtime.set_global(
            "array".into(),
            Value::Array(vec![
                Value::scalar("alpha"),
                Value::scalar("beta"),
                Value::scalar("gamma"),
            ]),
        );
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "test ALPHA test BETA test GAMMA ");
    }

    #[test]
    fn for_loop_parameters_with_variables() {
        let text = concat!(
            "{% assign l = 4 %}",
            "{% assign o = 5 %}",
            "{% for i in (1..100) limit:l offset:o %}",
            "{{ i }} ",
            "{% endfor %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "6 7 8 9 ");
    }

    #[test]
    fn tablerow_without_cols() {
        let text = concat!(
            "{% tablerow name in array %}",
            "test {{name}} ",
            "{% endtablerow %}",
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global(
            "array".into(),
            Value::Array(vec![
                Value::scalar(22f64),
                Value::scalar(23f64),
                Value::scalar(24f64),
                Value::scalar("wat".to_owned()),
            ]),
        );
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "<tr class=\"row1\"><td class=\"col1\">test 22 </td><td class=\"col2\">test 23 </td><td class=\"col3\">test 24 </td><td class=\"col4\">test wat </td></tr>");
    }

    #[test]
    fn tablerow_with_cols() {
        let text = concat!(
            "{% tablerow name in (42..46) cols:2 %}",
            "test {{name}} ",
            "{% endtablerow %}",
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global(
            "array".into(),
            Value::Array(vec![
                Value::scalar(22f64),
                Value::scalar(23f64),
                Value::scalar(24f64),
                Value::scalar("wat".to_owned()),
            ]),
        );
        let output = template.render(&runtime).unwrap();
        assert_eq!(
                output,
                "<tr class=\"row1\"><td class=\"col1\">test 42 </td><td class=\"col2\">test 43 </td></tr><tr class=\"row2\"><td class=\"col1\">test 44 </td><td class=\"col2\">test 45 </td></tr><tr class=\"row3\"><td class=\"col1\">test 46 </td></tr>"
            );
    }

    #[test]
    fn tablerow_loop_parameters_with_variables() {
        let text = concat!(
            "{% assign l = 4 %}",
            "{% assign o = 5 %}",
            "{% assign c = 3 %}",
            "{% tablerow i in (1..100) limit:l offset:o cols:c %}",
            "{{ i }} ",
            "{% endtablerow %}"
        );
        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "<tr class=\"row1\"><td class=\"col1\">6 </td><td class=\"col2\">7 </td><td class=\"col3\">8 </td></tr><tr class=\"row2\"><td class=\"col1\">9 </td></tr>");
    }

    #[test]
    fn tablerow_variables() {
        let text = concat!(
            "{% tablerow v in (100..103) cols:2 %}",
            "length: {{tablerow.length}}, ",
            "index: {{tablerow.index}}, ",
            "index0: {{tablerow.index0}}, ",
            "rindex: {{tablerow.rindex}}, ",
            "rindex0: {{tablerow.rindex0}}, ",
            "col: {{tablerow.col}}, ",
            "col0: {{tablerow.col0}}, ",
            "value: {{v}}, ",
            "first: {{tablerow.first}}, ",
            "last: {{tablerow.last}}, ",
            "col_first: {{tablerow.col_first}}, ",
            "col_last: {{tablerow.col_last}}",
            "{% endtablerow %}",
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        let output = template.render(&runtime).unwrap();
        assert_eq!(
                output,
                concat!(
    "<tr class=\"row1\"><td class=\"col1\">length: 4, index: 1, index0: 0, rindex: 4, rindex0: 3, col: 1, col0: 0, value: 100, first: true, last: false, col_first: true, col_last: false</td>",
    "<td class=\"col2\">length: 4, index: 2, index0: 1, rindex: 3, rindex0: 2, col: 2, col0: 1, value: 101, first: false, last: false, col_first: false, col_last: true</td></tr>",
    "<tr class=\"row2\"><td class=\"col1\">length: 4, index: 3, index0: 2, rindex: 2, rindex0: 1, col: 1, col0: 0, value: 102, first: false, last: false, col_first: true, col_last: false</td>",
    "<td class=\"col2\">length: 4, index: 4, index0: 3, rindex: 1, rindex0: 0, col: 2, col0: 1, value: 103, first: false, last: true, col_first: false, col_last: true</td></tr>",
    )
            );
    }

    #[test]
    fn test_for_parentloop_nil_when_not_present() {
        //NOTE: this test differs slightly from the liquid conformity test
        let text = concat!(
            "{% for inner in outer %}",
            // the liquid test has `forloop.parentloop.index` here
            "{{ forloop.parentloop }}.{{ forloop.index }} ",
            "{% endfor %}"
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global(
            "outer".into(),
            Value::Array(vec![
                Value::Array(vec![
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                ]),
                Value::Array(vec![
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                ]),
            ]),
        );
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, ".1 .2 ");
    }

    #[test]
    fn test_for_parentloop_references_parent_loop() {
        let text = concat!(
            "{% for inner in outer %}{% for k in inner %}",
            "{{ forloop.parentloop.index }}.{{ forloop.index }} ",
            "{% endfor %}{% endfor %}"
        );

        let template = parser::parse(text, &options())
            .map(runtime::Template::new)
            .unwrap();

        let runtime = RuntimeBuilder::new().build();
        runtime.set_global(
            "outer".into(),
            Value::Array(vec![
                Value::Array(vec![
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                ]),
                Value::Array(vec![
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                    Value::scalar(1f64),
                ]),
            ]),
        );
        let output = template.render(&runtime).unwrap();
        assert_eq!(output, "1.1 1.2 1.3 2.1 2.2 2.3 ");
    }
}
