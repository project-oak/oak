use liquid::ValueView;

#[test]
fn test_simple_variable() {
    assert_template_result!(r#"worked"#, r#"{{test}}"#, o!({"test": "worked"}));

    assert_template_result!(
        r#"worked wonderfully"#,
        r#"{{test}}"#,
        o!({"test": "worked wonderfully"}),
    );
}

#[test]
#[should_panic]
fn test_variable_render_calls_to_liquid() {
    panic!("to_liquid is implementation specific");
}

#[test]
fn test_simple_with_whitespaces() {
    assert_template_result!(r#"  worked  "#, r#"  {{ test }}  "#, o!({"test": "worked"}));

    assert_template_result!(
        r#"  worked wonderfully  "#,
        r#"  {{ test }}  "#,
        o!({"test": "worked wonderfully"}),
    );
}

#[test]
#[should_panic]
fn test_ignore_unknown() {
    assert_template_result!(r#""#, r#"{{ test }}"#);
    panic!("Requires `strict_variables: false`");
}

#[test]
fn test_using_blank_as_variable_name() {
    assert_template_result!(r#""#, r#"{% assign foo = blank %}{{ foo }}"#);
}

#[test]
fn test_using_empty_as_variable_name() {
    assert_template_result!(r#""#, r#"{% assign foo = empty %}{{ foo }}"#);
}

#[test]
fn test_hash_scoping() {
    assert_template_result!(
        r#"worked"#,
        r#"{{ test.test }}"#,
        o!({"test": {"test": "worked"}}),
    );
}

#[test]
fn test_false_renders_as_false() {
    assert_template_result!(r#"false"#, r#"{{ foo }}"#, o!({"foo": false}));

    assert_template_result!(r#"false"#, r#"{{ false }}"#);
}

#[test]
fn test_nil_renders_as_empty_string() {
    assert_template_result!(r#""#, r#"{{ nil }}"#);

    assert_template_result!(r#"cat"#, r#"{{ nil | append: 'cat' }}"#);
}

#[test]
#[should_panic]
fn test_preset_assigns() {
    panic!("Preset assigns are implementation specific");
}

#[test]
fn test_reuse_parsed_template() {
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(r#"{{ greeting }} {{ name }}"#)
        .unwrap();

    let globals = o!({"greeting": "Hello", "name": "Tobi"});
    let rendered = template.render(&globals).unwrap();
    assert_eq!("Hello Tobi", rendered);

    // Modified due to strict_variables: true
    let globals = o!({"greeting": "Hello", "unknown": "Tobi"});
    template.render(globals.as_object().unwrap()).unwrap_err();

    let globals = o!({"greeting": "Hello", "name": "Brian"});
    let rendered = template.render(&globals).unwrap();
    assert_eq!("Hello Brian", rendered);

    // Preset assign cases ("Goodbye")( are implementation specific
}

#[test]
fn test_assigns_not_polluted_from_template() {
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(r#"{{ test }}{% assign test = 'bar' %}{{ test }}"#)
        .unwrap();

    // All modified due to strict_variables: true

    let globals = o!({"test": "baz"});
    let rendered = template.render(&globals).unwrap();
    assert_eq!("bazbar", rendered);

    let globals = o!({"test": "baz"});
    let rendered = template.render(&globals).unwrap();
    assert_eq!("bazbar", rendered);

    let globals = o!({"test": "foo"});
    let rendered = template.render(&globals).unwrap();
    assert_eq!("foobar", rendered);

    let globals = o!({"test": "baz"});
    let rendered = template.render(&globals).unwrap();
    assert_eq!("bazbar", rendered);
}

#[test]
#[should_panic]
fn test_hash_with_default_proc() {
    panic!("Default proc is implementation specific");
}

#[test]
fn test_multiline_variable() {
    assert_template_result!(r#"worked"#, "{{\ntest\n}}", o!({"test": "worked"}));
}

#[test]
#[should_panic]
fn test_render_symbol() {
    panic!("Symbols are implementation specific");
}
