#[test]
fn test_for() {
    assert_template_result!(
        " yo  yo  yo  yo ",
        "{%for item in array%} yo {%endfor%}",
        o!({"array": [1, 2, 3, 4]}),
    );
    assert_template_result!(
        "yoyo",
        "{%for item in array%}yo{%endfor%}",
        o!({"array": [1, 2]}),
    );
    assert_template_result!(
        " yo ",
        "{%for item in array%} yo {%endfor%}",
        o!({"array": [1]}),
    );
    assert_template_result!("", "{%for item in array%}{%endfor%}", o!({"array": [1, 2]}));
    let expected = r#"

  yo

  yo

  yo

"#;
    let template = r#"
{%for item in array%}
  yo
{%endfor%}
"#;
    assert_template_result!(expected, template, o!({"array": [1, 2, 3]}));
}

#[test]
fn test_for_reversed() {
    let assigns = o!({ "array": [ 1, 2, 3] });
    assert_template_result!(
        "321",
        "{%for item in array reversed %}{{item}}{%endfor%}",
        assigns,
    );
}

#[test]
#[should_panic] // liquid-rust#273
fn test_for_with_range() {
    assert_template_result!(
        " 1  2  3 ",
        "{%for item in (1..3) %} {{item}} {%endfor%}",
        o!({}),
    );

    assert_render_error!("{% for i in (a..2) %}{% endfor %}", o!({"a": [1, 2]}));

    assert_template_result!(
        " 0  1  2  3 ",
        "{% for item in (a..3) %} {{item}} {% endfor %}",
        o!({"a": "invalid integer"}),
    );
}

#[test]
fn test_for_with_variable_range() {
    assert_template_result!(
        " 1  2  3 ",
        "{%for item in (1..foobar) %} {{item}} {%endfor%}",
        o!({"foobar": 3}),
    );
}

#[test]
fn test_for_with_hash_value_range() {
    let foobar = o!({ "value": 3 });
    assert_template_result!(
        " 1  2  3 ",
        "{%for item in (1..foobar.value) %} {{item}} {%endfor%}",
        o!({ "foobar": foobar }),
    );
}

#[test]
#[should_panic]
fn test_for_with_drop_value_range() {
    panic!("Implementation specific: docs");
}

#[test]
fn test_for_with_variable() {
    assert_template_result!(
        " 1  2  3 ",
        "{%for item in array%} {{item}} {%endfor%}",
        o!({"array": [1, 2, 3]}),
    );
    assert_template_result!(
        "123",
        "{%for item in array%}{{item}}{%endfor%}",
        o!({"array": [1, 2, 3]}),
    );
    assert_template_result!(
        "123",
        "{% for item in array %}{{item}}{% endfor %}",
        o!({"array": [1, 2, 3]}),
    );
    assert_template_result!(
        "abcd",
        "{%for item in array%}{{item}}{%endfor%}",
        o!({"array": ["a", "b", "c", "d"]}),
    );
    assert_template_result!(
        "a b c",
        "{%for item in array%}{{item}}{%endfor%}",
        o!({"array": ["a", " ", "b", " ", "c"]}),
    );
    assert_template_result!(
        "abc",
        "{%for item in array%}{{item}}{%endfor%}",
        o!({"array": ["a", "", "b", "", "c"]}),
    );
}

#[test]
fn test_for_helpers() {
    let assigns = o!({ "array": [1, 2, 3] });
    assert_template_result!(
        " 1/3  2/3  3/3 ",
        "{%for item in array%} {{forloop.index}}/{{forloop.length}} {%endfor%}",
        assigns,
    );
    assert_template_result!(
        " 1  2  3 ",
        "{%for item in array%} {{forloop.index}} {%endfor%}",
        assigns,
    );
    assert_template_result!(
        " 0  1  2 ",
        "{%for item in array%} {{forloop.index0}} {%endfor%}",
        assigns,
    );
    assert_template_result!(
        " 2  1  0 ",
        "{%for item in array%} {{forloop.rindex0}} {%endfor%}",
        assigns,
    );
    assert_template_result!(
        " 3  2  1 ",
        "{%for item in array%} {{forloop.rindex}} {%endfor%}",
        assigns,
    );
    assert_template_result!(
        " true  false  false ",
        "{%for item in array%} {{forloop.first}} {%endfor%}",
        assigns,
    );
    assert_template_result!(
        " false  false  true ",
        "{%for item in array%} {{forloop.last}} {%endfor%}",
        assigns,
    );
}

#[test]
fn test_for_and_if() {
    let assigns = o!({ "array": [1, 2, 3] });
    assert_template_result!(
        "+--",
        "{%for item in array%}{% if forloop.first %}+{% else %}-{% endif %}{%endfor%}",
        assigns,
    );
}

#[test]
fn test_for_else() {
    assert_template_result!(
        "+++",
        "{%for item in array%}+{%else%}-{%endfor%}",
        o!({"array": [1, 2, 3]}),
    );
    assert_template_result!(
        "-",
        "{%for item in array%}+{%else%}-{%endfor%}",
        o!({"array": []}),
    );
    assert_template_result!(
        "-",
        "{%for item in array%}+{%else%}-{%endfor%}",
        o!({ "array": nil }),
    );
}

#[test]
fn test_limiting() {
    let assigns = o!({ "array": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0] });
    assert_template_result!(
        "12",
        "{%for i in array limit:2 %}{{ i }}{%endfor%}",
        assigns,
    );
    assert_template_result!(
        "1234",
        "{%for i in array limit:4 %}{{ i }}{%endfor%}",
        assigns,
    );
    assert_template_result!(
        "3456",
        "{%for i in array limit:4 offset:2 %}{{ i }}{%endfor%}",
        assigns,
    );
    assert_template_result!(
        "3456",
        "{%for i in array limit: 4 offset: 2 %}{{ i }}{%endfor%}",
        assigns,
    );
}

#[test]
fn test_dynamic_variable_limiting() {
    let assigns = o!({ "array": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0], "limit": 2, "offset": 2 });

    assert_template_result!(
        "34",
        "{%for i in array limit: limit offset: offset %}{{ i }}{%endfor%}",
        assigns,
    );
}

#[test]
fn test_nested_for() {
    let assigns = o!({ "array": [[1, 2], [3, 4], [5, 6]] });
    assert_template_result!(
        "123456",
        "{%for item in array%}{%for i in item%}{{ i }}{%endfor%}{%endfor%}",
        assigns,
    );
}

#[test]
fn test_offset_only() {
    let assigns = o!({ "array": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0] });
    assert_template_result!(
        "890",
        "{%for i in array offset:7 %}{{ i }}{%endfor%}",
        assigns,
    );
}

#[test]
#[should_panic] // liquid-rust#274
fn test_pause_resume() {
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0] } });
    let markup = r#"
      {%for i in array.items limit: 3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit: 3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit: 3 %}{{i}}{%endfor%}
      "#;
    let expected = r#"
      123
      next
      456
      next
      789
      "#;
    assert_template_result!(expected, markup, assigns);
}

#[test]
#[should_panic] // liquid-rust#274
fn test_pause_resume_limit() {
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0] } });
    let markup = r#"
      {%for i in array.items limit:3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit:3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit:1 %}{{i}}{%endfor%}
      "#;
    let expected = r#"
      123
      next
      456
      next
      7
      "#;
    assert_template_result!(expected, markup, assigns);
}

#[test]
#[should_panic] // liquid-rust#274
fn test_pause_resume_big_limit() {
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0] } });
    let markup = r#"
      {%for i in array.items limit:3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit:3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit:1000 %}{{i}}{%endfor%}
      "#;
    let expected = r#"
      123
      next
      456
      next
      7890
      "#;
    assert_template_result!(expected, markup, assigns);
}

#[test]
#[should_panic] // liquid-rust#274
fn test_pause_resume_big_offset() {
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5, 6, 7, 8, 9, 0] } });
    let markup = "{%for i in array.items limit:3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit:3 %}{{i}}{%endfor%}
      next
      {%for i in array.items offset:continue limit:3 offset:1000 %}{{i}}{%endfor%}";
    let expected = "123
      next
      456
      next
      ";
    assert_template_result!(expected, markup, assigns);
}

#[test]
fn test_for_with_break() {
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] } });

    let markup = "{% for i in array.items %}{% break %}{% endfor %}";
    let expected = "";
    assert_template_result!(expected, markup, assigns);

    let markup = "{% for i in array.items %}{{ i }}{% break %}{% endfor %}";
    let expected = "1";
    assert_template_result!(expected, markup, assigns);

    let markup = "{% for i in array.items %}{% break %}{{ i }}{% endfor %}";
    let expected = "";
    assert_template_result!(expected, markup, assigns);

    let markup =
        "{% for i in array.items %}{{ i }}{% if i > 3 %}{% break %}{% endif %}{% endfor %}";
    let expected = "1234";
    assert_template_result!(expected, markup, assigns);

    // tests to ensure it only breaks out of the local for loop
    // and not all of them.
    let assigns = o!({ "array": [[1, 2], [3, 4], [5, 6]] });
    let markup = concat!(
        "{% for item in array %}",
        "{% for i in item %}",
        "{% if i == 1 %}",
        "{% break %}",
        "{% endif %}",
        "{{ i }}",
        "{% endfor %}",
        "{% endfor %}"
    );
    let expected = "3456";
    assert_template_result!(expected, markup, assigns);

    // test break does nothing when unreached
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5] } });
    let markup =
        "{% for i in array.items %}{% if i == 9999 %}{% break %}{% endif %}{{ i }}{% endfor %}";
    let expected = "12345";
    assert_template_result!(expected, markup, assigns);
}

#[test]
fn test_for_with_continue() {
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5] } });

    let markup = "{% for i in array.items %}{% continue %}{% endfor %}";
    let expected = "";
    assert_template_result!(expected, markup, assigns);

    let markup = "{% for i in array.items %}{{ i }}{% continue %}{% endfor %}";
    let expected = "12345";
    assert_template_result!(expected, markup, assigns);

    let markup = "{% for i in array.items %}{% continue %}{{ i }}{% endfor %}";
    let expected = "";
    assert_template_result!(expected, markup, assigns);

    let markup =
        "{% for i in array.items %}{% if i > 3 %}{% continue %}{% endif %}{{ i }}{% endfor %}";
    let expected = "123";
    assert_template_result!(expected, markup, assigns);

    let markup = "{% for i in array.items %}{% if i == 3 %}{% continue %}{% else %}{{ i }}{% endif %}{% endfor %}";
    let expected = "1245";
    assert_template_result!(expected, markup, assigns);

    // tests to ensure it only continues the local for loop and not all of them.
    let assigns = o!({ "array": [[1, 2], [3, 4], [5, 6]] });
    let markup = concat!(
        "{% for item in array %}",
        "{% for i in item %}",
        "{% if i == 1 %}",
        "{% continue %}",
        "{% endif %}",
        "{{ i }}",
        "{% endfor %}",
        "{% endfor %}"
    );
    let expected = "23456";
    assert_template_result!(expected, markup, assigns);

    // test continue does nothing when unreached
    let assigns = o!({ "array": { "items": [1, 2, 3, 4, 5] } });
    let markup =
        "{% for i in array.items %}{% if i == 9999 %}{% continue %}{% endif %}{{ i }}{% endfor %}";
    let expected = "12345";
    assert_template_result!(expected, markup, assigns);
}

#[test]
#[should_panic] // liquid-rust#270
fn test_for_tag_string() {
    // ruby 1.8.7 "String".each: Enumerator with single "String" element.
    // ruby 1.9.3 no longer supports .each on String though we mimic
    // the functionality for backwards compatibility

    assert_template_result!(
        "test string",
        "{%for val in string%}{{val}}{%endfor%}",
        o!({"string": "test string"}),
    );

    assert_template_result!(
        "test string",
        "{%for val in string limit:1%}{{val}}{%endfor%}",
        o!({"string": "test string"}),
    );

    assert_template_result!(
        "val-string-1-1-0-1-0-true-true-test string",
        concat!(
            "{%for val in string%}",
            "{{forloop.name}}-",
            "{{forloop.index}}-",
            "{{forloop.length}}-",
            "{{forloop.index0}}-",
            "{{forloop.rindex}}-",
            "{{forloop.rindex0}}-",
            "{{forloop.first}}-",
            "{{forloop.last}}-",
            "{{val}}{%endfor%}"
        ),
        o!({"string": "test string"}),
    );
}

#[test]
fn test_for_parentloop_references_parent_loop() {
    assert_template_result!(
        "1.1 1.2 1.3 2.1 2.2 2.3 ",
        concat!(
            "{% for inner in outer %}{% for k in inner %}",
            "{{ forloop.parentloop.index }}.{{ forloop.index }} ",
            "{% endfor %}{% endfor %}"
        ),
        o!({"outer": [[1, 1, 1], [1, 1, 1]]}),
    );
}

#[test]
#[should_panic] // liquid-rust#271
fn test_for_parentloop_nil_when_not_present() {
    assert_template_result!(
        ".1 .2 ",
        concat!(
            "{% for inner in outer %}",
            "{{ forloop.parentloop.index }}.{{ forloop.index }} ",
            "{% endfor %}"
        ),
        o!({"outer": [[1, 1, 1], [1, 1, 1]]}),
    );
}

#[test]
fn test_inner_for_over_empty_input() {
    assert_template_result!(
        "oo",
        "{% for a in (1..2) %}o{% for b in empty %}{% endfor %}{% endfor %}",
        o!({}),
    );
}

#[test]
#[should_panic] // liquid-rust#270
fn test_blank_string_not_iterable() {
    assert_template_result!(
        "",
        "{% for char in characters %}I WILL NOT BE OUTPUT{% endfor %}",
        o!({"characters": ""}),
    );
}

#[test]
fn test_bad_variable_naming_in_for_loop() {
    assert_parse_error!("{% for a/b in x %}{% endfor %}");
}

#[test]
fn test_spacing_with_variable_naming_in_for_loop() {
    let expected = "12345";
    let template = "{% for       item   in   items %}{{item}}{% endfor %}";
    let assigns = o!({ "items": [1, 2, 3, 4, 5] });
    assert_template_result!(expected, template, assigns);
}

#[test]
#[should_panic]
fn test_iterate_with_each_when_no_limit_applied() {
    panic!("Implementation specific: `each` is a ruby thing");
}

#[test]
#[should_panic]
fn test_iterate_with_load_slice_when_limit_applied() {
    panic!("Implementation specific: `each` is a ruby thing");
}

#[test]
#[should_panic]
fn test_iterate_with_load_slice_when_limit_and_offset_applied() {
    panic!("Implementation specific: `each` is a ruby thing");
}

#[test]
#[should_panic]
fn test_iterate_with_load_slice_returns_same_results_as_without() {
    panic!("Implementation specific: `each` is a ruby thing");
}

#[test]
#[should_panic]
fn test_for_cleans_up_registers() {
    panic!("Implementation specific: API detail");
}
