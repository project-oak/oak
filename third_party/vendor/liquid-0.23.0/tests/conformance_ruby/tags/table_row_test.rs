#[test]
#[should_panic] // liquid-rust#282
fn test_table_row() {
    assert_template_result!(
        "<tr class=\"row1\">\n<td class=\"col1\"> 1 </td><td class=\"col2\"> 2 </td><td class=\"col3\"> 3 </td></tr>\n<tr class=\"row2\"><td class=\"col1\"> 4 </td><td class=\"col2\"> 5 </td><td class=\"col3\"> 6 </td></tr>\n",
        "{% tablerow n in numbers cols:3%} {{n}} {% endtablerow %}",
        o!({"numbers": [1, 2, 3, 4, 5, 6]}));

    assert_template_result!(
        "<tr class=\"row1\">\n</tr>\n",
        "{% tablerow n in numbers cols:3%} {{n}} {% endtablerow %}",
        o!({"numbers": []}),
    );
}

#[test]
#[should_panic] // liquid-rust#282
fn test_table_row_with_different_cols() {
    assert_template_result!(
        "<tr class=\"row1\">\n<td class=\"col1\"> 1 </td><td class=\"col2\"> 2 </td><td class=\"col3\"> 3 </td><td class=\"col4\"> 4 </td><td class=\"col5\"> 5 </td></tr>\n<tr class=\"row2\"><td class=\"col1\"> 6 </td></tr>\n",
        "{% tablerow n in numbers cols:5%} {{n}} {% endtablerow %}",
        o!({"numbers": [1, 2, 3, 4, 5, 6]}));
}

#[test]
#[should_panic] // liquid-rust#282
fn test_table_col_counter() {
    assert_template_result!(
        "<tr class=\"row1\">\n<td class=\"col1\">1</td><td class=\"col2\">2</td></tr>\n<tr class=\"row2\"><td class=\"col1\">1</td><td class=\"col2\">2</td></tr>\n<tr class=\"row3\"><td class=\"col1\">1</td><td class=\"col2\">2</td></tr>\n",
        "{% tablerow n in numbers cols:2%}{{tablerowloop.col}}{% endtablerow %}",
        o!({"numbers": [1, 2, 3, 4, 5, 6]}));
}

#[test]
#[should_panic] // liquid-rust#282
fn test_quoted_fragment() {
    assert_template_result!(
        "<tr class=\"row1\">\n<td class=\"col1\"> 1 </td><td class=\"col2\"> 2 </td><td class=\"col3\"> 3 </td></tr>\n<tr class=\"row2\"><td class=\"col1\"> 4 </td><td class=\"col2\"> 5 </td><td class=\"col3\"> 6 </td></tr>\n",
        "{% tablerow n in collections.frontpage cols:3%} {{n}} {% endtablerow %}",
        o!({"collections": { "frontpage": [1, 2, 3, 4, 5, 6] }}));
    assert_template_result!(
        "<tr class=\"row1\">\n<td class=\"col1\"> 1 </td><td class=\"col2\"> 2 </td><td class=\"col3\"> 3 </td></tr>\n<tr class=\"row2\"><td class=\"col1\"> 4 </td><td class=\"col2\"> 5 </td><td class=\"col3\"> 6 </td></tr>\n",
        r#"{% tablerow n in collections["frontpage"] cols:3%} {{n}} {% endtablerow %}"#,
        o!({"collections": { "frontpage": [1, 2, 3, 4, 5, 6] }}));
}

#[test]
#[should_panic]
fn test_enumerable_drop() {
    panic!("Implementation specific: drop support");
}

#[test]
#[should_panic] // liquid-rust#282
fn test_offset_and_limit() {
    assert_template_result!(
        "<tr class=\"row1\">\n<td class=\"col1\"> 1 </td><td class=\"col2\"> 2 </td><td class=\"col3\"> 3 </td></tr>\n<tr class=\"row2\"><td class=\"col1\"> 4 </td><td class=\"col2\"> 5 </td><td class=\"col3\"> 6 </td></tr>\n",
        "{% tablerow n in numbers cols:3 offset:1 limit:6%} {{n}} {% endtablerow %}",
        o!({"numbers": [0, 1, 2, 3, 4, 5, 6, 7]}));
}

#[test]
fn test_blank_string_not_iterable() {
    // Implementation specific: adapted from a lax case.
    assert_render_error!(
        "{% tablerow char in characters cols:3 %}I WILL NOT BE OUTPUT{% endtablerow %}",
        o!({"characters": ""}),
    );
}
