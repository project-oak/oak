// tests that no weird errors are raised if continue is called outside of a
// block
#[test]
fn test_break_with_no_block() {
    let assigns = o!({});
    let markup = "{% continue %}";
    let expected = "";

    assert_template_result!(expected, markup, assigns);
}
