#[test]
fn test_unexpected_outer_tag() {
    assert_parse_error!(r#"{% else %}"#);
}

#[test]
fn test_unknown_tag() {
    assert_parse_error!(r#"{% foo %}"#);
}
