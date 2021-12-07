#[test]
fn test_unexpected_end_tag() {
    assert_parse_error!(r#"{% if true %}{% endunless %}"#);
}
