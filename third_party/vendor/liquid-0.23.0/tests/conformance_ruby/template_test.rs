#[test]
#[should_panic]
fn test_instance_assigns_persist_on_same_template_object_between_parses() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_warnings_is_not_exponential_time() {
    panic!("Implementation specific: warnings API");
}

#[test]
#[should_panic]
fn test_instance_assigns_persist_on_same_template_parsing_between_renders() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_custom_assigns_do_not_persist_on_same_template() {
    panic!("Implementation specific: parse API");
}

#[test]
#[should_panic]
fn test_custom_assigns_squash_instance_assigns() {
    panic!("Implementation specific: parse API");
}

#[test]
#[should_panic]
fn test_persistent_assigns_squash_instance_assigns() {
    panic!("Implementation specific: parse API");
}

#[test]
#[should_panic]
fn test_lambda_is_called_once_from_persistent_assigns_over_multiple_parses_and_renders() {
    panic!("Implementation specific: parse API");
}

#[test]
#[should_panic]
fn test_lambda_is_called_once_from_custom_assigns_over_multiple_parses_and_renders() {
    panic!("Implementation specific: parse API");
}

#[test]
#[should_panic]
fn test_resource_limits_works_with_custom_length_method() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_resource_limits_render_length() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_resource_limits_render_score() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_resource_limits_assign_score() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_resource_limits_assign_score_nested() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_resource_limits_aborts_rendering_after_first_error() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_resource_limits_hash_in_template_gets_updated_even_if_no_limits_are_set() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_render_length_persists_between_blocks() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_default_resource_limits_unaffected_by_render_with_runtime() {
    panic!("Implementation specific: render API");
}

#[test]
#[should_panic]
fn test_can_use_drop_as_runtime() {
    panic!("Implementation specific: drops");
}

#[test]
#[should_panic]
fn test_render_bang_force_rethrow_errors_on_passed_runtime() {
    panic!("Implementation specific: error API");
}

#[test]
#[should_panic]
fn test_exception_renderer_that_returns_string() {
    panic!("Implementation specific: error API");
}

#[test]
#[should_panic]
fn test_exception_renderer_that_raises() {
    panic!("Implementation specific: error API");
}

#[test]
#[should_panic]
fn test_global_filter_option_on_render() {
    panic!("Implementation specific: global filters");
}

#[test]
#[should_panic]
fn test_global_filter_option_when_native_filters_exist() {
    panic!("Implementation specific: global filters");
}

#[test]
#[should_panic]
fn test_undefined_variables() {
    panic!("Implementation specific: error API");
}

#[test]
fn test_nil_value_does_not_raise() {
    assert_template_result!("something", "some{{x}}thing", o!({ "x": nil }));
}

#[test]
fn test_undefined_variables_raise() {
    assert_render_error!(
        "{{x}} {{y}} {{z.a}} {{z.b}} {{z.c.d}}",
        o!({ "x": 33, "z": { "a": 32, "c": { "e": 31 } } }),
    );
}

#[test]
#[should_panic]
fn test_undefined_drop_methods() {
    panic!("Implementation specific: drops");
}

#[test]
#[should_panic]
fn test_undefined_drop_methods_raise() {
    panic!("Implementation specific: drops");
}

#[test]
#[should_panic]
fn test_undefined_filters() {
    panic!("Implementation specific: error API");
}

#[test]
#[should_panic] // liquid-rust#284
fn test_undefined_filters_raise() {
    assert_render_error!("{x | somefilter1 | upcase | somefilter2}", o!({"x": "foo"}));
}

#[test]
#[should_panic] // liquid-rust#224
fn test_using_range_literal_works_as_expected() {
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse("{% assign foo = (x..y) %}{{ foo }}")
        .unwrap();
    let rendered = template.render(&o!({"x": 1, "y": 5})).unwrap();
    assert_eq!("1..5", rendered);

    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse("{% assign nums = (x..y) %}{% for num in nums %}{{ num }}{% endfor %}")
        .unwrap();
    let rendered = template.render(&o!({"x": 1, "y": 5})).unwrap();
    assert_eq!("12345", rendered);
}
