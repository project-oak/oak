#[macro_use]
extern crate difference;

use liquid::*;
use std::fs::File;
use std::io::Read;

fn compare_by_file(name: &str, globals: &Object) {
    let input_file = format!("tests/fixtures/input/{}.txt", name);
    let output_file = format!("tests/fixtures/output/{}.txt", name);

    let template = ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse_file(input_file)
        .unwrap();

    let output = template.render(globals).unwrap();

    let mut comp = String::new();
    File::open(output_file)
        .unwrap()
        .read_to_string(&mut comp)
        .unwrap();

    assert_diff!(&comp, &output, " ", 0);
}

#[test]
pub fn error_on_nonexistent_file() {
    let template = ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse_file("not-a-file.ext");
    assert!(template.is_err());
}

#[test]
pub fn example_by_file() {
    let globals = object!({
        "num": 5,
        "numTwo": 6
    });
    compare_by_file("example", &globals);
}
