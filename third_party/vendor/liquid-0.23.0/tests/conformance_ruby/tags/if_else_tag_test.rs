#[test]
fn test_if() {
    assert_template_result!(
        "  ",
        " {% if false %} this text should not go into the output {% endif %} "
    );
    assert_template_result!(
        "  this text should go into the output  ",
        " {% if true %} this text should go into the output {% endif %} "
    );
    assert_template_result!(
        "  you rock ?",
        "{% if false %} you suck {% endif %} {% if true %} you rock {% endif %}?"
    );
}

#[test]
fn test_literal_comparisons() {
    assert_template_result!(
        " NO ",
        "{% assign v = false %}{% if v %} YES {% else %} NO {% endif %}"
    );
    assert_template_result!(
        " YES ",
        "{% assign v = nil %}{% if v == nil %} YES {% else %} NO {% endif %}"
    );
}

#[test]
fn test_if_else() {
    assert_template_result!(" YES ", "{% if false %} NO {% else %} YES {% endif %}");
    assert_template_result!(" YES ", "{% if true %} YES {% else %} NO {% endif %}");
    assert_template_result!(" YES ", r#"{% if "foo" %} YES {% else %} NO {% endif %}"#);
}

#[test]
fn test_if_boolean() {
    assert_template_result!(" YES ", "{% if var %} YES {% endif %}", o!({"var": true}));
}

#[test]
fn test_if_or() {
    assert_template_result!(
        " YES ",
        "{% if a or b %} YES {% endif %}",
        o!({"a": true, "b": true})
    );
    assert_template_result!(
        " YES ",
        "{% if a or b %} YES {% endif %}",
        o!({"a": true, "b": false})
    );
    assert_template_result!(
        " YES ",
        "{% if a or b %} YES {% endif %}",
        o!({"a": false, "b": true})
    );
    assert_template_result!(
        "",
        "{% if a or b %} YES {% endif %}",
        o!({"a": false, "b": false})
    );

    assert_template_result!(
        " YES ",
        "{% if a or b or c %} YES {% endif %}",
        o!({"a": false, "b": false, "c": true})
    );
    assert_template_result!(
        "",
        "{% if a or b or c %} YES {% endif %}",
        o!({"a": false, "b": false, "c": false})
    );
}

#[test]
fn test_if_or_with_operators() {
    assert_template_result!(
        " YES ",
        "{% if a == true or b == true %} YES {% endif %}",
        o!({"a": true, "b": true})
    );
    assert_template_result!(
        " YES ",
        "{% if a == true or b == false %} YES {% endif %}",
        o!({"a": true, "b": true})
    );
    assert_template_result!(
        "",
        "{% if a == false or b == false %} YES {% endif %}",
        o!({"a": true, "b": true})
    );
}

#[test]
fn test_comparison_of_strings_containing_and_or_or() {
    let mut awful_markup = "{% if ".to_owned();
    awful_markup.push_str(r#"a == "and" and b == "or" and c == "foo and bar" and d == "bar or baz" and e == "foo" and foo and bar"#);
    awful_markup.push_str(" %}");
    awful_markup.push_str(" YES {% endif %}");
    let assigns = o!({ "a": "and", "b": "or", "c": "foo and bar", "d": "bar or baz", "e": "foo", "foo": true, "bar": true });
    assert_template_result!(" YES ", awful_markup, assigns);
}

#[test]
fn test_comparison_of_expressions_starting_with_and_or_or() {
    let assigns = o!({ "order": { "items_count": 0 }, "android": { "name": "Roy" } });
    assert_template_result!(
        "YES",
        r#"{% if android.name == "Roy" %}YES{% endif %}"#,
        assigns
    );
    assert_template_result!(
        "YES",
        "{% if order.items_count == 0 %}YES{% endif %}",
        assigns
    );
}

#[test]
fn test_if_and() {
    assert_template_result!(" YES ", "{% if true and true %} YES {% endif %}");
    assert_template_result!("", "{% if false and true %} YES {% endif %}");
    assert_template_result!("", "{% if false and true %} YES {% endif %}");
}

#[test]
fn test_hash_miss_generates_false() {
    assert_template_result!("", "{% if foo.bar %} NO {% endif %}", o!({"foo": {}}));
}

#[test]
fn test_if_from_variable() {
    assert_template_result!("", "{% if var %} NO {% endif %}", o!({"var": false}));
    assert_template_result!("", "{% if var %} NO {% endif %}", o!({ "var": nil }));
    assert_template_result!(
        "",
        "{% if foo.bar %} NO {% endif %}",
        o!({"foo": { "bar": false }})
    );
    assert_template_result!("", "{% if foo.bar %} NO {% endif %}", o!({"foo": {}}));
    assert_template_result!("", "{% if foo.bar %} NO {% endif %}", o!({ "foo": nil }));
    assert_template_result!("", "{% if foo.bar %} NO {% endif %}", o!({"foo": true}));

    assert_template_result!(" YES ", "{% if var %} YES {% endif %}", o!({"var": "text"}));
    assert_template_result!(" YES ", "{% if var %} YES {% endif %}", o!({"var": true}));
    assert_template_result!(" YES ", "{% if var %} YES {% endif %}", o!({"var": 1}));
    assert_template_result!(" YES ", "{% if var %} YES {% endif %}", o!({"var": {}}));
    assert_template_result!(" YES ", "{% if var %} YES {% endif %}", o!({"var": []}));
    assert_template_result!(" YES ", r#"{% if "foo" %} YES {% endif %}"#);
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% endif %}",
        o!({"foo": { "bar": true }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% endif %}",
        o!({"foo": { "bar": "text" }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% endif %}",
        o!({"foo": { "bar": 1 }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% endif %}",
        o!({"foo": { "bar": {} }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% endif %}",
        o!({"foo": { "bar": [] }})
    );

    assert_template_result!(
        " YES ",
        "{% if var %} NO {% else %} YES {% endif %}",
        o!({"var": false})
    );
    assert_template_result!(
        " YES ",
        "{% if var %} NO {% else %} YES {% endif %}",
        o!({ "var": nil })
    );
    assert_template_result!(
        " YES ",
        "{% if var %} YES {% else %} NO {% endif %}",
        o!({"var": true})
    );
    assert_template_result!(
        " YES ",
        r#"{% if "foo" %} YES {% else %} NO {% endif %}"#,
        o!({"var": "text"})
    );

    assert_template_result!(
        " YES ",
        "{% if foo.bar %} NO {% else %} YES {% endif %}",
        o!({"foo": { "bar": false }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% else %} NO {% endif %}",
        o!({"foo": { "bar": true }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} YES {% else %} NO {% endif %}",
        o!({"foo": { "bar": "text" }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} NO {% else %} YES {% endif %}",
        o!({"foo": { "notbar": true }})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} NO {% else %} YES {% endif %}",
        o!({"foo": {}})
    );
    assert_template_result!(
        " YES ",
        "{% if foo.bar %} NO {% else %} YES {% endif %}",
        o!({"notfoo": { "bar": true }})
    );
}

#[test]
fn test_nested_if() {
    assert_template_result!("", "{% if false %}{% if false %} NO {% endif %}{% endif %}");
    assert_template_result!("", "{% if false %}{% if true %} NO {% endif %}{% endif %}");
    assert_template_result!("", "{% if true %}{% if false %} NO {% endif %}{% endif %}");
    assert_template_result!(
        " YES ",
        "{% if true %}{% if true %} YES {% endif %}{% endif %}"
    );

    assert_template_result!(
        " YES ",
        "{% if true %}{% if true %} YES {% else %} NO {% endif %}{% else %} NO {% endif %}"
    );
    assert_template_result!(
        " YES ",
        "{% if true %}{% if false %} NO {% else %} YES {% endif %}{% else %} NO {% endif %}"
    );
    assert_template_result!(
        " YES ",
        "{% if false %}{% if true %} NO {% else %} NONO {% endif %}{% else %} YES {% endif %}"
    );
}

#[test]
fn test_comparisons_on_null() {
    assert_template_result!("", "{% if null < 10 %} NO {% endif %}");
    assert_template_result!("", "{% if null <= 10 %} NO {% endif %}");
    assert_template_result!("", "{% if null >= 10 %} NO {% endif %}");
    assert_template_result!("", "{% if null > 10 %} NO {% endif %}");

    assert_template_result!("", "{% if 10 < null %} NO {% endif %}");
    assert_template_result!("", "{% if 10 <= null %} NO {% endif %}");
    assert_template_result!("", "{% if 10 >= null %} NO {% endif %}");
    assert_template_result!("", "{% if 10 > null %} NO {% endif %}");
}

#[test]
fn test_else_if() {
    assert_template_result!(
        "0",
        "{% if 0 == 0 %}0{% elsif 1 == 1%}1{% else %}2{% endif %}"
    );
    assert_template_result!(
        "1",
        "{% if 0 != 0 %}0{% elsif 1 == 1%}1{% else %}2{% endif %}"
    );
    assert_template_result!(
        "2",
        "{% if 0 != 0 %}0{% elsif 1 != 1%}1{% else %}2{% endif %}"
    );

    assert_template_result!("elsif", "{% if false %}if{% elsif true %}elsif{% endif %}");
}

#[test]
fn test_syntax_error_no_variable() {
    // Modified: since missing variables are render errors, we would hit a syntax error due to no
    // close block, preventing us from testing the real thing.
    assert_render_error!("{% if jerry == 1 %}{% endif %}");
}

#[test]
fn test_syntax_error_no_expression() {
    assert_parse_error!("{% if %}");
}

#[test]
#[should_panic]
fn test_if_with_custom_condition() {
    panic!("Implementation specific: API");
}

#[test]
#[ignore]
fn test_operators_are_ignored_unless_isolated() {
    panic!("TODO: Figure out what this is testing");
    /*
      original_op = Condition.operators["contains"]
      Condition.operators["contains"] = :[]

      assert_template_result!("yes",
        %({% if "gnomeslab-and-or-liquid" contains "gnomeslab-and-or-liquid" %}yes{% endif %}))
    ensure
      Condition.operators["contains"] = original_op*/
}

#[test]
fn test_operators_are_whitelisted() {
    assert_parse_error!(r#"{% if 1 or throw or or 1 %}yes{% endif %}"#);
}

#[test]
fn test_multiple_conditions() {
    let tpl = "{% if a or b and c %}true{% else %}false{% endif %}";

    let tests = vec![
        ((true, true, true), "true"),
        ((true, true, false), "true"),
        ((true, false, true), "true"),
        ((true, false, false), "true"),
        ((false, true, true), "true"),
        ((false, true, false), "false"),
        ((false, false, true), "false"),
        ((false, false, false), "false"),
    ];

    for (vals, expected) in tests {
        let (a, b, c) = vals;
        let assigns = o!({ "a": a, "b": b, "c": c });
        assert_template_result!(expected, tpl, assigns);
    }
}
