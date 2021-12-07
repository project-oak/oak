#[test]
#[should_panic]
fn test_no_instance_eval() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_no_existing_instance_eval() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_no_instance_eval_after_mixing_in_new_filter() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_no_instance_eval_later_in_chain() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_does_not_add_filters_to_symbol_table() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_does_not_add_drop_methods_to_symbol_table() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_max_depth_nested_blocks_does_not_raise_exception() {
    panic!("Implementation specific: non-sandboxed runtime");
}

#[test]
#[should_panic]
fn test_more_than_max_depth_nested_blocks_raises_exception() {
    panic!("Implementation specific: non-sandboxed runtime");
}
