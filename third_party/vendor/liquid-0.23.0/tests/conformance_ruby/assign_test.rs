#[test]
fn test_assign_with_hyphen_in_variable_name() {
    let template_source = r#"
    {% assign this-thing = 'Print this-thing' %}
    {{ this-thing }}
"#;
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(template_source)
        .unwrap();
    let rendered = template.render(&liquid::Object::default()).unwrap();

    assert_eq!("Print this-thing", rendered.trim());
}

#[test]
fn test_assigned_variable() {
    assert_template_result!(
        r#".foo."#,
        r#"{% assign foo = values %}.{{ foo[0] }}."#,
        o!({"values": ["foo", "bar", "baz"]}),
    );

    assert_template_result!(
        r#".bar."#,
        r#"{% assign foo = values %}.{{ foo[1] }}."#,
        o!({"values": ["foo", "bar", "baz"]}),
    );
}

#[test]
fn test_assign_with_filter() {
    assert_template_result!(
        r#".bar."#,
        r#"{% assign foo = values | split: "," %}.{{ foo[1] }}."#,
        o!({"values": "foo,bar,baz"}),
    );
}

#[test]
fn test_assign_syntax_error() {
    assert_parse_error!(r#"{% assign foo not values %}."#);
}

#[test]
fn test_assign_uses_error_mode() {
    assert_parse_error!(r#"{% assign foo = ('X' | downcase) %}"#);
}
