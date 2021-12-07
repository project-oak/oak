#[test]
fn test_inc() {
    assert_template_result!("0", "{%increment port %}", o!({}));
    assert_template_result!("0 1", "{%increment port %} {%increment port%}", o!({}));
    assert_template_result!("0 0 1 2 1",
      "{%increment port %} {%increment starboard%} {%increment port %} {%increment port%} {%increment starboard %}",
      o!({}));
}

#[test]
#[should_panic] // liquid-rust#276
fn test_dec() {
    assert_template_result!("9", "{%decrement port %}", o!({ "port": 10 }));
    assert_template_result!("-1 -2", "{%decrement port %} {%decrement port%}", o!({}));
    assert_template_result!("1 5 2 2 5",
      "{%increment port %} {%increment starboard%} {%increment port %} {%decrement port%} {%decrement starboard %}",
      o!({ "port": 1, "starboard": 5 }));
}
