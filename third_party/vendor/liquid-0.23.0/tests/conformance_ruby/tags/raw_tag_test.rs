#[test]
fn test_tag_in_raw() {
    assert_template_result!(
        "{% comment %} test {% endcomment %}",
        "{% raw %}{% comment %} test {% endcomment %}{% endraw %}",
    );
}

#[test]
fn test_output_in_raw() {
    assert_template_result!("{{ test }}", "{% raw %}{{ test }}{% endraw %}");
}

#[test]
fn test_open_tag_in_raw() {
    assert_template_result!(
        " Foobar {% invalid ",
        "{% raw %} Foobar {% invalid {% endraw %}",
    );
    assert_template_result!(
        " Foobar invalid %} ",
        "{% raw %} Foobar invalid %} {% endraw %}",
    );
    assert_template_result!(
        " Foobar {{ invalid ",
        "{% raw %} Foobar {{ invalid {% endraw %}",
    );
    assert_template_result!(
        " Foobar invalid }} ",
        "{% raw %} Foobar invalid }} {% endraw %}",
    );
    assert_template_result!(
        " Foobar {% invalid {% {% endraw ",
        "{% raw %} Foobar {% invalid {% {% endraw {% endraw %}",
    );
    assert_template_result!(
        " Foobar {% {% {% ",
        "{% raw %} Foobar {% {% {% {% endraw %}",
    );
    assert_template_result!(
        " test {% raw %} {% endraw %}",
        "{% raw %} test {% raw %} {% {% endraw %}endraw %}",
    );
    assert_template_result!(
        " Foobar {{ invalid 1",
        "{% raw %} Foobar {{ invalid {% endraw %}{{ 1 }}",
    );
}

#[test]
fn test_invalid_raw() {
    assert_parse_error!("{% raw %} foo");
    assert_parse_error!("{% raw } foo {% endraw %}");
    assert_parse_error!("{% raw } foo %}{% endraw %}");
}
