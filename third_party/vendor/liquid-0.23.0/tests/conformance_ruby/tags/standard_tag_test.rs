#[test]
fn test_no_transform() {
    assert_template_result!(
        "this text should come out of the template without change...",
        "this text should come out of the template without change..."
    );

    assert_template_result!("blah", "blah");
    assert_template_result!("<blah>", "<blah>");
    assert_template_result!("|,.:", "|,.:");
    assert_template_result!("", "");

    let text = r#"this shouldnt see any transformation either but has multiple lines
              as you can clearly see here ..."#;
    assert_template_result!(text, text);
}

#[test]
fn test_has_a_block_which_does_nothing() {
    assert_template_result!(
        "the comment block should be removed  .. right?",
        "the comment block should be removed {%comment%} be gone.. {%endcomment%} .. right?"
    );

    assert_template_result!("", "{%comment%}{%endcomment%}");
    assert_template_result!("", "{%comment%}{% endcomment %}");
    assert_template_result!("", "{% comment %}{%endcomment%}");
    assert_template_result!("", "{% comment %}{% endcomment %}");
    assert_template_result!("", "{%comment%}comment{%endcomment%}");
    assert_template_result!("", "{% comment %}comment{% endcomment %}");
    assert_template_result!(
        "",
        "{% comment %} 1 {% comment %} 2 {% endcomment %} 3 {% endcomment %}"
    );

    assert_template_result!("", "{%comment%}{%blabla%}{%endcomment%}");
    assert_template_result!("", "{% comment %}{% blabla %}{% endcomment %}");
    assert_template_result!("", "{%comment%}{% endif %}{%endcomment%}");
    assert_template_result!("", "{% comment %}{% endwhatever %}{% endcomment %}");
    assert_template_result!("", "{% comment %}{% raw %} {{%%%%}}  }} { {% endcomment %} {% comment {% endraw %} {% endcomment %}");

    assert_template_result!("foobar", "foo{%comment%}comment{%endcomment%}bar");
    assert_template_result!("foobar", "foo{% comment %}comment{% endcomment %}bar");
    assert_template_result!("foobar", "foo{%comment%} comment {%endcomment%}bar");
    assert_template_result!("foobar", "foo{% comment %} comment {% endcomment %}bar");

    assert_template_result!("foo  bar", "foo {%comment%} {%endcomment%} bar");
    assert_template_result!("foo  bar", "foo {%comment%}comment{%endcomment%} bar");
    assert_template_result!("foo  bar", "foo {%comment%} comment {%endcomment%} bar");

    assert_template_result!(
        "foobar",
        r#"foo{%comment%}
                                     {%endcomment%}bar"#
    );
}

#[test]
fn test_hyphenated_assign() {
    let assigns = o!({ "a-b": "1" });
    assert_template_result!(
        "a-b:1 a-b:2",
        "a-b:{{a-b}} {%assign a-b = 2 %}a-b:{{a-b}}",
        assigns
    );
}

#[test]
fn test_assign_with_colon_and_spaces() {
    let assigns = o!({ "var": { "a:b c": { "paged": "1" } } });
    assert_template_result!(
        "var2: 1",
        r#"{%assign var2 = var["a:b c"].paged %}var2: {{var2}}"#,
        assigns
    );
}

#[test]
fn test_capture() {
    // Implementation specific: strict_variables is enabled, testing that instead.
    let assigns = o!({ "var": "content" });
    assert_template_result!(
        "content foo content foo ",
        "{% capture var2 %}{{ var }} foo {% endcapture %}{{ var2 }}{{ var2 }}",
        assigns
    );
}

#[test]
fn test_capture_detects_bad_syntax() {
    // Implementation specific: strict_variables is enabled, testing that instead.
    assert_parse_error!("{% capture %}{{ var }} foo {% endcapture %}{{ var2 }}{{ var2 }}");
}

#[test]
fn test_case() {
    let assigns = o!({ "condition": 2 });
    assert_template_result!(
        " its 2 ",
        "{% case condition %}{% when 1 %} its 1 {% when 2 %} its 2 {% endcase %}",
        assigns
    );

    let assigns = o!({ "condition": 1 });
    assert_template_result!(
        " its 1 ",
        "{% case condition %}{% when 1 %} its 1 {% when 2 %} its 2 {% endcase %}",
        assigns
    );

    let assigns = o!({ "condition": 3 });
    assert_template_result!(
        "",
        "{% case condition %}{% when 1 %} its 1 {% when 2 %} its 2 {% endcase %}",
        assigns
    );

    let assigns = o!({ "condition": "string here" });
    assert_template_result!(
        " hit ",
        r#"{% case condition %}{% when "string here" %} hit {% endcase %}"#,
        assigns
    );

    let assigns = o!({ "condition": "bad string here" });
    assert_template_result!(
        "",
        r#"{% case condition %}{% when "string here" %} hit {% endcase %}"#,
        assigns
    );
}

#[test]
fn test_case_with_else() {
    let assigns = o!({ "condition": 5 });
    assert_template_result!(
        " hit ",
        "{% case condition %}{% when 5 %} hit {% else %} else {% endcase %}",
        assigns
    );

    let assigns = o!({ "condition": 6 });
    assert_template_result!(
        " else ",
        "{% case condition %}{% when 5 %} hit {% else %} else {% endcase %}",
        assigns
    );

    let assigns = o!({ "condition": 6 });
    assert_template_result!(
        " else ",
        "{% case condition %} {% when 5 %} hit {% else %} else {% endcase %}",
        assigns
    );
}

#[test]
fn test_case_on_size() {
    assert_template_result!(
        "",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}",
        o!({"a": []})
    );
    assert_template_result!(
        "1",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}",
        o!({"a": [1]})
    );
    assert_template_result!(
        "2",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}",
        o!({"a": [1, 1]})
    );
    assert_template_result!(
        "",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}",
        o!({"a": [1, 1, 1]})
    );
    assert_template_result!(
        "",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}",
        o!({"a": [1, 1, 1, 1]})
    );
    assert_template_result!(
        "",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% endcase %}",
        o!({"a": [1, 1, 1, 1, 1]})
    );
}

#[test]
fn test_case_on_size_with_else() {
    assert_template_result!(
        "else",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}",
        o!({"a": []})
    );

    assert_template_result!(
        "1",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}",
        o!({"a": [1]})
    );

    assert_template_result!(
        "2",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}",
        o!({"a": [1, 1]})
    );

    assert_template_result!(
        "else",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}",
        o!({"a": [1, 1, 1]})
    );

    assert_template_result!(
        "else",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}",
        o!({"a": [1, 1, 1, 1]})
    );

    assert_template_result!(
        "else",
        "{% case a.size %}{% when 1 %}1{% when 2 %}2{% else %}else{% endcase %}",
        o!({"a": [1, 1, 1, 1, 1]})
    );
}

#[test]
#[should_panic] // liquid-rust#278
fn test_case_on_length_with_else() {
    assert_template_result!(
        "else",
        "{% case a.empty? %}{% when true %}true{% when false %}false{% else %}else{% endcase %}"
    );

    assert_template_result!(
        "false",
        "{% case false %}{% when true %}true{% when false %}false{% else %}else{% endcase %}"
    );

    assert_template_result!(
        "true",
        "{% case true %}{% when true %}true{% when false %}false{% else %}else{% endcase %}"
    );

    assert_template_result!(
        "else",
        "{% case NULL %}{% when true %}true{% when false %}false{% else %}else{% endcase %}"
    );
}

#[test]
fn test_assign_from_case() {
    // Example from the shopify forums
    let code = r#"{% case collection.handle %}{% when "menswear-jackets" %}{% assign ptitle = "menswear" %}{% when "menswear-t-shirts" %}{% assign ptitle = "menswear" %}{% else %}{% assign ptitle = "womenswear" %}{% endcase %}{{ ptitle }}"#;
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse(code)
        .unwrap();

    assert_eq!(
        "menswear",
        template
            .render(&o!({"collection": { "handle": "menswear-jackets" }}))
            .unwrap()
    );
    assert_eq!(
        "menswear",
        template
            .render(&o!({"collection": { "handle": "menswear-t-shirts" }}))
            .unwrap()
    );
    assert_eq!(
        "womenswear",
        template
            .render(&o!({"collection": { "handle": "x" }}))
            .unwrap()
    );
    assert_eq!(
        "womenswear",
        template
            .render(&o!({"collection": { "handle": "y" }}))
            .unwrap()
    );
    assert_eq!(
        "womenswear",
        template
            .render(&o!({"collection": { "handle": "z" }}))
            .unwrap()
    );
}

#[test]
fn test_case_when_or() {
    let code = "{% case condition %}{% when 1 or 2 or 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}";
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 1 }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 2 }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 3 }));
    assert_template_result!(" its 4 ", code, o!({ "condition": 4 }));
    assert_template_result!("", code, o!({ "condition": 5 }));

    let code = r#"{% case condition %}{% when 1 or "string" or null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}"#;
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 1 }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": "string" }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": nil }));
    assert_template_result!("", code, o!({ "condition": "something else" }));
}

#[test]
fn test_case_when_comma() {
    let code =
        "{% case condition %}{% when 1, 2, 3 %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}";
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 1 }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 2 }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 3 }));
    assert_template_result!(" its 4 ", code, o!({ "condition": 4 }));
    assert_template_result!("", code, o!({ "condition": 5 }));

    let code = r#"{% case condition %}{% when 1, "string", null %} its 1 or 2 or 3 {% when 4 %} its 4 {% endcase %}"#;
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": 1 }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": "string" }));
    assert_template_result!(" its 1 or 2 or 3 ", code, o!({ "condition": nil }));
    assert_template_result!("", code, o!({ "condition": "something else" }));
}

#[test]
fn test_assign() {
    assert_template_result!("variable", r#"{% assign a = "variable"%}{{a}}"#);
}

#[test]
fn test_assign_unassigned() {
    // Implementation specific: strict_variables is enabled, testing that instead.
    let assigns = o!({ "var": "content" });
    assert_render_error!("var2:{{var2}} {%assign var2 = var%} var2:{{var2}}", assigns);
}

#[test]
fn test_assign_an_empty_string() {
    assert_template_result!("", r#"{% assign a = ""%}{{a}}"#);
}

#[test]
fn test_assign_is_global() {
    assert_template_result!(
        "variable",
        r#"{%for i in (1..2) %}{% assign a = "variable"%}{% endfor %}{{a}}"#
    );
}

#[test]
fn test_case_detects_bad_syntax() {
    assert_parse_error!("{% case false %}{% when %}true{% endcase %}");

    assert_parse_error!("{% case false %}{% huh %}true{% endcase %}");
}

#[test]
fn test_cycle() {
    assert_template_result!("one", r#"{%cycle "one", "two"%}"#);
    assert_template_result!(
        "one two",
        r#"{%cycle "one", "two"%} {%cycle "one", "two"%}"#
    );
    assert_template_result!(" two", r#"{%cycle "", "two"%} {%cycle "", "two"%}"#);

    assert_template_result!(
        "one two one",
        r#"{%cycle "one", "two"%} {%cycle "one", "two"%} {%cycle "one", "two"%}"#
    );

    assert_template_result!(
        "text-align: left text-align: right",
        r#"{%cycle "text-align: left", "text-align: right" %} {%cycle "text-align: left", "text-align: right"%}"#
    );
}

#[test]
fn test_multiple_cycles() {
    assert_template_result!("1 2 1 1 2 3 1",
      "{%cycle 1,2%} {%cycle 1,2%} {%cycle 1,2%} {%cycle 1,2,3%} {%cycle 1,2,3%} {%cycle 1,2,3%} {%cycle 1,2,3%}");
}

#[test]
fn test_multiple_named_cycles() {
    assert_template_result!(
        "one one two two one one",
        r#"{%cycle 1: "one", "two" %} {%cycle 2: "one", "two" %} {%cycle 1: "one", "two" %} {%cycle 2: "one", "two" %} {%cycle 1: "one", "two" %} {%cycle 2: "one", "two" %}"#
    );
}

#[test]
fn test_multiple_named_cycles_with_names_from_runtime() {
    let assigns = o!({ "var1": 1, "var2": 2 });
    assert_template_result!(
        "one one two two one one",
        r#"{%cycle var1: "one", "two" %} {%cycle var2: "one", "two" %} {%cycle var1: "one", "two" %} {%cycle var2: "one", "two" %} {%cycle var1: "one", "two" %} {%cycle var2: "one", "two" %}"#,
        assigns
    );
}

#[test]
fn test_size_of_array() {
    let assigns = o!({ "array": [1, 2, 3, 4] });
    assert_template_result!(
        "array has 4 elements",
        "array has {{ array.size }} elements",
        assigns
    );
}

#[test]
fn test_size_of_hash() {
    let assigns = o!({ "hash": { "a": 1, "b": 2, "c": 3, "d": 4 } });
    assert_template_result!(
        "hash has 4 elements",
        "hash has {{ hash.size }} elements",
        assigns
    );
}

#[test]
fn test_illegal_symbols() {
    assert_template_result!("", "{% if true == empty %}?{% endif %}");
    assert_template_result!("", "{% if true == null %}?{% endif %}");
    assert_template_result!("", "{% if empty == true %}?{% endif %}");
    assert_template_result!("", "{% if null == true %}?{% endif %}");
}

#[test]
fn test_ifchanged() {
    let assigns = o!({ "array": [ 1, 1, 2, 2, 3, 3] });
    assert_template_result!(
        "123",
        "{%for item in array%}{%ifchanged%}{{item}}{% endifchanged %}{%endfor%}",
        assigns
    );

    let assigns = o!({ "array": [ 1, 1, 1, 1] });
    assert_template_result!(
        "1",
        "{%for item in array%}{%ifchanged%}{{item}}{% endifchanged %}{%endfor%}",
        assigns
    );
}

#[test]
fn test_multiline_tag() {
    assert_template_result!(
        "0 1 2 3",
        "0{%\nfor i in (1..3)\n%} {{\ni\n}}{%\nendfor\n%}"
    );
}
