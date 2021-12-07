#[test]
#[should_panic]
fn test_templates_parsed_with_line_numbers_renders_them_in_errors() {
    panic!("Implementation specific: lax errors");
}

#[test]
#[should_panic]
fn test_standard_error() {
    panic!("Implementation specific: error types");
}

#[test]
#[should_panic]
fn test_syntax() {
    panic!("Implementation specific: error types");
}

#[test]
#[should_panic]
fn test_argument() {
    panic!("Implementation specific: error types");
}

#[test]
fn test_missing_endtag_parse_time_error() {
    assert_parse_error!(" {% for a in b %} ... ");
}

#[test]
fn test_unrecognized_operator() {
    assert_parse_error!(" {% if 1 =! 2 %}ok{% endif %} ");
}

#[test]
#[should_panic]
fn test_lax_unrecognized_operator() {
    panic!("Implementation specific: lax errors");
}

#[test]
#[should_panic]
fn test_with_line_numbers_adds_numbers_to_parser_errors() {
    panic!("Implementation specific: lax errors");
}

#[test]
#[should_panic]
fn test_with_line_numbers_adds_numbers_to_parser_errors_with_whitespace_trim() {
    panic!("Implementation specific: lax errors");
}

#[test]
#[should_panic]
fn test_parsing_warn_with_line_numbers_adds_numbers_to_lexer_errors() {
    panic!("Implementation specific: lax errors");
}

#[test]
fn test_parsing_strict_with_line_numbers_adds_numbers_to_lexer_errors() {
    let err = assert_parse_error!(
        r#"
          foobar

          {% if 1 =! 2 %}ok{% endif %}

          bla
    "#,
    );
    let err = err.to_string();

    println!("err={}", err);
    assert!(err.contains("4 |"));
}

#[test]
#[should_panic] // liquid-rust#247
fn test_syntax_errors_in_nested_blocks_have_correct_line_number() {
    let err = assert_parse_error!(
        r#"
          foobar

          {% if 1 != 2 %}
            {% foo %}
          {% endif %}

          bla
    "#,
    );
    let err = err.to_string();

    let expected = regex::Regex::new(r#"\bline 5\b"#).unwrap();
    println!("err={}", err);
    assert!(expected.is_match(&err));
}

#[test]
#[should_panic]
fn test_strict_error_messages() {
    panic!("Implementation specific: error format");
}

#[test]
#[should_panic]
fn test_warnings() {
    panic!("Implementation specific: lax errors");
}

#[test]
#[should_panic]
fn test_warning_line_numbers() {
    panic!("Implementation specific: lax errors");
}

#[test]
#[should_panic]
fn test_exceptions_propagate() {
    panic!("Implementation specific: error propagation");
}

#[test]
#[should_panic]
fn test_default_exception_renderer_with_internal_error() {
    panic!("Implementation specific: error propagation");
}

#[test]
#[should_panic]
fn test_setting_default_exception_renderer() {
    panic!("Implementation specific: error propagation");
}

#[test]
#[should_panic]
fn test_exception_renderer_exposing_non_liquid_error() {
    panic!("Implementation specific: error propagation");
}

#[test]
fn test_included_template_name_with_line_numbers() {
    /*old_file_system = Liquid::Template.file_system

    begin
      Liquid::Template.file_system = TestFileSystem.new
      template = Liquid::Template.parse("Argument error:\n{% include 'product' %}", line_numbers: true)
      page = template.render('errors' => ErrorDrop.new)
    ensure
      Liquid::Template.file_system = old_file_system
    end
    assert_equal "Argument error:\nLiquid error (product line 1): argument error", page
    assert_equal "product", template.errors.first.template_name*/
}
