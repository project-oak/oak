#[macro_use]
extern crate difference;

use liquid::*;

fn compare(input: &str, expected: &str) {
    let input = input.replace("…", " ");
    let expected = expected.replace("…", " ");

    let template = ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(&input)
        .unwrap();

    let output = template.render(&Object::default()).unwrap();

    assert_diff!(&expected, &output, " ", 0);
}

#[test]
pub fn no_whitespace_control() {
    compare(
        "
topic1
……{% assign foo = \"bar\" %}
……{% if foo %}
…………-……{{ foo }}
……{% endif %}
",
        "
topic1
……
……
…………-……bar
……
",
    );
}

#[test]
pub fn simple_whitespace_control() {
    compare(
        "
topic1
……{% assign foo = \"bar\" -%}
……{% if foo -%}
…………-……{{- foo }}
……{%- endif %}
",
        "
topic1
……-bar
",
    );
}

#[test]
pub fn double_sided_whitespace_control() {
    compare(
        "
topic1
……{%- assign foo = \"bar\" -%}
……-……{{- foo -}}……

",
        "
topic1-bar\
",
    );
}
