use std::borrow;

const N: usize = 10;

fn wrap_in_for<S: AsRef<str>>(body: S) -> String {
    let mut result = String::new();
    result.push_str("{% for i in (1..10) %}");
    result.push_str(body.as_ref());
    result.push_str("{% endfor %}");
    result
}

fn wrap_in_if<S: AsRef<str>>(body: S) -> String {
    let mut result = String::new();
    result.push_str("{% if true %}");
    result.push_str(body.as_ref());
    result.push_str("{% endif %}");
    result
}

fn wrap<S: AsRef<str>>(body: S) -> String {
    let body = body.as_ref();
    let mut result = wrap_in_for(body);
    result.push_str(&wrap_in_if(body));
    result
}

fn repeat<S: AsRef<str>>(content: S, count: usize) -> String {
    let content = content.as_ref();
    (0..count).map(|_| content).collect::<String>()
}

#[derive(Default, Debug, Clone, Copy)]
struct BlankTestFilesystem;

impl liquid::partials::PartialSource for BlankTestFilesystem {
    fn contains(&self, _name: &str) -> bool {
        true
    }

    fn names(&self) -> Vec<&str> {
        vec![]
    }

    fn try_get<'a>(&'a self, name: &str) -> Option<borrow::Cow<'a, str>> {
        Some(name.to_owned().into())
    }
}

#[test]
fn test_new_tags_are_not_blank_by_default() {
    assert_template_result!(
        repeat(" ", N),
        wrap_in_for("{{ foobar }}"),
        o!({"foobar": " "}),
    );
}

#[test]
#[should_panic] // liquid-rust#244
fn test_loops_are_blank() {
    assert_template_result!("", wrap_in_for(" "));
}

#[test]
#[should_panic] // liquid-rust#244
fn test_if_else_are_blank() {
    assert_template_result!("", "{% if true %} {% elsif false %} {% else %} {% endif %}",);
}

#[test]
fn test_unless_is_blank() {
    assert_template_result!("", wrap("{% unless true %} {% endunless %}"));
}

#[test]
fn test_mark_as_blank_only_during_parsing() {
    assert_template_result!(
        repeat(" ", N + 1),
        wrap(" {% if false %} this never happens, but still, this block is not blank {% endif %}"),
    );
}

#[test]
#[should_panic] // liquid-rust#244
fn test_comments_are_blank() {
    assert_template_result!("", wrap(" {% comment %} whatever {% endcomment %} "),);
}

#[test]
#[should_panic] // liquid-rust#244
fn test_captures_are_blank() {
    assert_template_result!("", wrap(" {% capture foo %} whatever {% endcapture %} "),);
}

#[test]
#[should_panic] // liquid-rust#244
fn test_nested_blocks_are_blank_but_only_if_all_children_are() {
    assert_template_result!("", &wrap(wrap(" ")));
    assert_template_result!(
        repeat("\n       but this is not ", N + 1),
        wrap(
            "{% if true %} {% comment %} this is blank {% endcomment %} {% endif %}
      {% if true %} but this is not {% endif %}",
        ),
    );
}

#[test]
#[should_panic] // liquid-rust#244
fn test_assigns_are_blank() {
    assert_template_result!("", &wrap(r#" {% assign foo = "bar" %} "#));
}

#[test]
#[should_panic] // liquid-rust#244
fn test_whitespace_is_blank() {
    assert_template_result!("", wrap(" "));
    assert_template_result!("", wrap("\t"));
}

#[test]
fn test_whitespace_is_not_blank_if_other_stuff_is_present() {
    let body = "     x ";
    assert_template_result!(repeat(body, N + 1), wrap(&body));
}

#[test]
fn test_increment_is_not_blank() {
    assert_template_result!(
        repeat(" 0", 2 * (N + 1)),
        wrap("{% assign foo = 0 %} {% increment foo %} {% decrement foo %}"),
        o!({}),
    );
}

#[test]
fn test_cycle_is_not_blank() {
    assert_template_result!(repeat(" ", N + 1), wrap("{% cycle ' ', ' ' %}"));
}

#[test]
fn test_raw_is_not_blank() {
    assert_template_result!(repeat("  ", N + 1), wrap(" {% raw %} {% endraw %}"), o!({}),);
}

#[test]
fn test_include_is_blank() {
    let liquid = liquid::ParserBuilder::with_stdlib()
        .partials(liquid::partials::OnDemandCompiler::<BlankTestFilesystem>::empty())
        .build()
        .unwrap();

    assert_template_result!(
        repeat("foobar", N + 1),
        wrap("{% include 'foobar' %}"),
        o!({}),
        liquid
    );
    assert_template_result!(
        repeat(" foobar ", N + 1),
        wrap("{% include ' foobar ' %}"),
        o!({}),
        liquid
    );
    assert_template_result!(
        repeat("   ", N + 1),
        wrap(" {% include ' ' %} "),
        o!({}),
        liquid
    );
}

#[test]
#[should_panic] // liquid-rust#244
fn test_case_is_blank() {
    assert_template_result!("", wrap(" {% assign foo = 'bar' %} {% case foo %} {% when 'bar' %} {% when 'whatever' %} {% else %} {% endcase %} "));
    assert_template_result!("", wrap(" {% assign foo = 'else' %} {% case foo %} {% when 'bar' %} {% when 'whatever' %} {% else %} {% endcase %} "));
    assert_template_result!(repeat("   x  ", N+1), wrap(" {% assign foo = 'else' %} {% case foo %} {% when 'bar' %} {% when 'whatever' %} {% else %} x {% endcase %} "));
}
