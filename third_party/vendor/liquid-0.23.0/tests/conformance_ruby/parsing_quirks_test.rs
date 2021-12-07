#[test]
fn test_parsing_css() {
    let text = " div { font-weight: bold; } ";
    assert_template_result!(text, text);
}

#[test]
fn test_raise_on_single_close_bracet() {
    assert_parse_error!("text {{method} oh nos!");
}

#[test]
fn test_raise_on_label_and_no_close_bracets() {
    assert_parse_error!("TEST {{ ");
}

#[test]
fn test_raise_on_label_and_no_close_bracets_percent() {
    assert_parse_error!("TEST {% ");
}

#[test]
fn test_error_on_empty_filter() {
    // Implementation specific: lax parser

    assert_parse_error!("{{|test}}");
    assert_parse_error!("{{test |a|b|}}");
}

#[test]
fn test_meaningless_parens_error() {
    assert_parse_error!(
        "{% if a == 'foo' or (b == 'bar' and c == 'baz') or false %} YES {% endif %}",
    );
}

#[test]
fn test_unexpected_characters_syntax_error() {
    assert_parse_error!("{% if true && false %} YES {% endif %}");
    assert_parse_error!("{% if false || true %} YES {% endif %}");
}

#[test]
#[should_panic]
fn test_no_error_on_lax_empty_filter() {
    panic!("Implementation specific: lax parser");
}

#[test]
#[should_panic]
fn test_meaningless_parens_lax() {
    panic!("Implementation specific: lax parser");
}

#[test]
#[should_panic]
fn test_unexpected_characters_silently_eat_logic_lax() {
    panic!("Implementation specific: lax parser");
}

#[test]
fn test_raise_on_invalid_tag_delimiter() {
    assert_parse_error!("{% end %}");
}

#[test]
#[should_panic]
fn test_unanchored_filter_arguments() {
    panic!("Implementation specific: lax parser");
}

#[test]
#[should_panic]
fn test_invalid_variables_work() {
    panic!("Implementation specific: lax parser");
}

#[test]
#[should_panic]
fn test_extra_dots_in_ranges() {
    panic!("Implementation specific: lax parser");
}

#[test]
fn test_contains_in_id() {
    assert_template_result!(
        " YES ",
        "{% if containsallshipments == true %} YES {% endif %}",
        o!({"containsallshipments": true}),
    );
}
