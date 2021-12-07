#[test]
#[should_panic] // liquid-rust#245
fn test_captures_block_content_in_variable() {
    assert_template_result!(
        r#"test string"#,
        r#"{% capture 'var' %}test string{% endcapture %}{{var}}"#,
    );
}

#[test]
fn test_capture_with_hyphen_in_variable_name() {
    let template_source = r#"
    {% capture this-thing %}Print this-thing{% endcapture %}
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
fn test_capture_to_variable_from_outer_scope_if_existing() {
    let template_source = r#"
    {% assign var = '' %}
    {% if true %}
    {% capture var %}first-block-string{% endcapture %}
    {% endif %}
    {% if true %}
    {% capture var %}test-string{% endcapture %}
    {% endif %}
    {{var}}
"#;
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(template_source)
        .unwrap();
    let rendered = template.render(&liquid::Object::default()).unwrap();

    assert_eq!("test-string", rendered.trim());
}

#[test]
fn test_assigning_from_capture() {
    let template_source = r#"
    {% assign first = '' %}
    {% assign second = '' %}
    {% for number in (1..3) %}
    {% capture first %}{{number}}{% endcapture %}
    {% assign second = first %}
    {% endfor %}
    {{ first }}-{{ second }}
"#;
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(template_source)
        .unwrap();
    let rendered = template.render(&liquid::Object::default()).unwrap();

    assert_eq!("3-3", rendered.trim());
}
