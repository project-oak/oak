use liquid_core::Expression;
use liquid_core::Result;
use liquid_core::Runtime;
use liquid_core::{Display_filter, Filter, FilterParameters, FilterReflection, ParseFilter};
use liquid_core::{Value, ValueView};

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "make_funny",
    description = "tests helper",
    parsed(MakeFunnyFilter)
)]
pub struct MakeFunnyFilterParser;

#[derive(Debug, Default, Display_filter)]
#[name = "make_funny"]
pub struct MakeFunnyFilter;

impl Filter for MakeFunnyFilter {
    fn evaluate(&self, _input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        Ok(Value::scalar("LOL"))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "cite_funny",
    description = "tests helper",
    parsed(CiteFunnyFilter)
)]
pub struct CiteFunnyFilterParser;

#[derive(Debug, Default, Display_filter)]
#[name = "cite_funny"]
pub struct CiteFunnyFilter;

impl Filter for CiteFunnyFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        Ok(Value::scalar(format!("LOL: {}", input.render())))
    }
}

#[derive(Debug, FilterParameters)]
struct AddSmileyFilterParameters {
    #[parameter(description = "", arg_type = "str")]
    smiley: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "add_smiley",
    description = "tests helper",
    parameters(AddSmileyFilterParameters),
    parsed(AddSmileyFilter)
)]
pub struct AddSmileyFilterParser;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "add_smiley"]
pub struct AddSmileyFilter {
    #[parameters]
    args: AddSmileyFilterParameters,
}

impl Filter for AddSmileyFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;
        let smiley = args.smiley.unwrap_or_else(|| ":-)".into()).to_string();
        Ok(Value::scalar(format!("{} {}", input.render(), smiley)))
    }
}

#[derive(Debug, FilterParameters)]
struct AddTagFilterParameters {
    #[parameter(description = "", arg_type = "str")]
    tag: Option<Expression>,

    #[parameter(description = "", arg_type = "str")]
    id: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "add_tag",
    description = "tests helper",
    parameters(AddTagFilterParameters),
    parsed(AddTagFilter)
)]
pub struct AddTagFilterParser;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "add_tag"]
pub struct AddTagFilter {
    #[parameters]
    args: AddTagFilterParameters,
}

impl Filter for AddTagFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let tag = args.tag.unwrap_or_else(|| "p".into()).to_string();
        let id = args.id.unwrap_or_else(|| "foo".into()).to_string();
        Ok(Value::scalar(format!(
            r#"<{} id="{}">{}</{}>"#,
            tag,
            id,
            input.render(),
            tag
        )))
    }
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "paragraph",
    description = "tests helper",
    parsed(ParagraphFilter)
)]
pub struct ParagraphFilterParser;

#[derive(Debug, Default, Display_filter)]
#[name = "paragraph"]
pub struct ParagraphFilter;

impl Filter for ParagraphFilter {
    fn evaluate(&self, input: &dyn ValueView, _runtime: &dyn Runtime) -> Result<Value> {
        Ok(Value::scalar(format!("<p>{}</p>", input.render())))
    }
}

#[derive(Debug, FilterParameters)]
struct LinkToFilterParameters {
    #[parameter(description = "", arg_type = "str")]
    url: Option<Expression>,
}

#[derive(Clone, ParseFilter, FilterReflection)]
#[filter(
    name = "link_to",
    description = "tests helper",
    parameters(LinkToFilterParameters),
    parsed(LinkToFilter)
)]
pub struct LinkToFilterParser;

#[derive(Debug, FromFilterParameters, Display_filter)]
#[name = "link_to"]
pub struct LinkToFilter {
    #[parameters]
    args: LinkToFilterParameters,
}

impl Filter for LinkToFilter {
    fn evaluate(&self, input: &dyn ValueView, runtime: &dyn Runtime) -> Result<Value> {
        let args = self.args.evaluate(runtime)?;

        let name = input;
        let url = args.url.unwrap_or_else(|| ":-)".into()).to_string();
        Ok(Value::scalar(format!(
            r#"<a href="{}">{}</a>"#,
            url,
            name.render()
        )))
    }
}

fn liquid() -> liquid::Parser {
    liquid::ParserBuilder::new()
        .filter(MakeFunnyFilterParser)
        .filter(CiteFunnyFilterParser)
        .filter(AddSmileyFilterParser)
        .filter(AddTagFilterParser)
        .filter(ParagraphFilterParser)
        .filter(LinkToFilterParser)
        .build()
        .unwrap()
}

fn assigns() -> liquid::Object {
    o!({
      "best_cars": "bmw",
      "car": { "bmw": "good", "gm": "bad" }
    })
}

#[test]
fn test_variable() {
    let text = " {{best_cars}} ";

    let expected = " bmw ";
    assert_template_result!(expected, text, assigns());
}

#[test]
fn test_variable_traversing_with_two_brackets() {
    let text = "{{ site.data.menu[include.menu][include.locale] }}";
    assert_template_result!(
        "it works!",
        text,
        o!({
          "site": { "data": { "menu": { "foo": { "bar": "it works!" } } } },
          "include": { "menu": "foo", "locale": "bar" }
        })
    );
}

#[test]
fn test_variable_traversing() {
    let text = " {{car.bmw}} {{car.gm}} {{car.bmw}} ";

    let expected = " good bad good ";
    assert_template_result!(expected, text, assigns());
}

#[test]
fn test_variable_piping() {
    let text = " {{ car.gm | make_funny }} ";
    let expected = " LOL ";

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_variable_piping_with_input() {
    let text = " {{ car.gm | cite_funny }} ";
    let expected = " LOL: bad ";

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_variable_piping_with_args() {
    let text = r#" {{ car.gm | add_smiley : ":-(" }} "#;
    let expected = " bad :-( ";

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_variable_piping_with_no_args() {
    let text = " {{ car.gm | add_smiley }} ";
    let expected = " bad :-) ";

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_multiple_variable_piping_with_args() {
    let text = r#" {{ car.gm | add_smiley : ":-(" | add_smiley : ":-("}} "#;
    let expected = " bad :-( :-( ";

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_variable_piping_with_multiple_args() {
    let text = r#" {{ car.gm | add_tag : "span", "bar"}} "#;
    let expected = r#" <span id="bar">bad</span> "#;

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_variable_piping_with_variable_args() {
    let text = r#" {{ car.gm | add_tag : "span", car.bmw}} "#;
    let expected = r#" <span id="good">bad</span> "#;

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_multiple_pipings() {
    let text = " {{ best_cars | cite_funny | paragraph }} ";
    let expected = " <p>LOL: bmw</p> ";

    assert_template_result!(expected, text, assigns(), liquid());
}

#[test]
fn test_link_to() {
    let text = r#" {{ "Typo" | link_to: "http://typo.leetsoft.com" }} "#;
    let expected = r#" <a href="http://typo.leetsoft.com">Typo</a> "#;

    assert_template_result!(expected, text, assigns(), liquid());
}
