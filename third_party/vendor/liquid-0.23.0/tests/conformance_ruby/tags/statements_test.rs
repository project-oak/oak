#[test]
fn test_true_eql_true() {
    let text = " {% if true == true %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text);
}

#[test]
fn test_true_not_eql_true() {
    let text = " {% if true != true %} true {% else %} false {% endif %} ";
    assert_template_result!("  false  ", text);
}

#[test]
fn test_true_lq_true() {
    let text = " {% if 0 > 0 %} true {% else %} false {% endif %} ";
    assert_template_result!("  false  ", text);
}

#[test]
fn test_one_lq_zero() {
    let text = " {% if 1 > 0 %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text);
}

#[test]
fn test_zero_lq_one() {
    let text = " {% if 0 < 1 %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text);
}

#[test]
fn test_zero_lq_or_equal_one() {
    let text = " {% if 0 <= 0 %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text);
}

#[test]
fn test_zero_lq_or_equal_one_involving_nil() {
    let text = " {% if null <= 0 %} true {% else %} false {% endif %} ";
    assert_template_result!("  false  ", text);

    let text = " {% if 0 <= null %} true {% else %} false {% endif %} ";
    assert_template_result!("  false  ", text);
}

#[test]
fn test_zero_lqq_or_equal_one() {
    let text = " {% if 0 >= 0 %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text);
}

#[test]
fn test_strings() {
    let text = " {% if 'test' == 'test' %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text);
}

#[test]
fn test_strings_not_equal() {
    let text = " {% if 'test' != 'test' %} true {% else %} false {% endif %} ";
    assert_template_result!("  false  ", text);
}

#[test]
fn test_var_strings_equal() {
    let text = r#" {% if var == "hello there!" %} true {% else %} false {% endif %} "#;
    assert_template_result!("  true  ", text, o!({"var": "hello there!"}));
}

#[test]
fn test_var_strings_are_not_equal() {
    let text = r#" {% if "hello there!" == var %} true {% else %} false {% endif %} "#;
    assert_template_result!("  true  ", text, o!({"var": "hello there!"}));
}

#[test]
fn test_var_and_long_string_are_equal() {
    let text = r#" {% if var == "hello there!" %} true {% else %} false {% endif %} "#;
    assert_template_result!("  true  ", text, o!({"var": "hello there!"}));
}

#[test]
fn test_var_and_long_string_are_equal_backwards() {
    let text = r#" {% if "hello there!" == var %} true {% else %} false {% endif %} "#;
    assert_template_result!("  true  ", text, o!({"var": "hello there!"}));
}

/*
  # def test_is_nil
  #  text = %| {% if var != nil %} true {% else %} false {% end %} |
  #  @template.assigns = { "var": "hello there!"}
  #  expected = %|  true  |
  #  assert_equal expected, @template.parse(text)
  # end
*/

#[test]
fn test_is_collection_empty() {
    let text = " {% if array == empty %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text, o!({"array": []}));
}

#[test]
fn test_is_not_collection_empty() {
    let text = " {% if array == empty %} true {% else %} false {% endif %} ";
    assert_template_result!("  false  ", text, o!({"array": [1, 2, 3]}));
}

#[test]
fn test_nil() {
    let text = " {% if var == nil %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text, o!({ "var": nil }));

    let text = " {% if var == null %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text, o!({ "var": nil }));
}

#[test]
fn test_not_nil() {
    let text = " {% if var != nil %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text, o!({"var": 1}));

    let text = " {% if var != null %} true {% else %} false {% endif %} ";
    assert_template_result!("  true  ", text, o!({"var": 1}));
}
