use liquid_lib::jekyll;

#[test]
fn test_slugify_default() {
    assert_eq!(
        liquid_core::call_filter!(jekyll::Slugify, " Q*bert says @!#@!").unwrap(),
        v!("q-bert-says"),
    );
}

#[test]
fn test_slugify_pretty() {
    assert_eq!(
        liquid_core::call_filter!(jekyll::Slugify, " Q*bert says _@!#?@!", "pretty").unwrap(),
        v!("q-bert-says-_@!-@!"),
    );
}
