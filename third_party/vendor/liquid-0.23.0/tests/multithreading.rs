#[macro_use]
extern crate difference;

use std::fs::File;
use std::io::Read;
use std::sync::Arc;
use std::thread;

#[test]
pub fn pass_between_threads() {
    let input_file = "tests/fixtures/input/example.txt";
    let template = liquid::ParserBuilder::with_stdlib()
        .build()
        .unwrap()
        .parse_file(&input_file)
        .unwrap();
    let template = Arc::new(template);

    // Start threads
    let mut handles = Vec::new();
    let v = vec![(5f64, 6f64), (20f64, 10f64)];
    for (counter, (num1, num2)) in v.into_iter().enumerate() {
        let template = Arc::clone(&template);
        let output_file = format!("tests/fixtures/output/example_mt{}.txt", counter + 1);
        handles.push(thread::spawn(move || {
            let globals = liquid::object!({
                "num": num1,
                "numTwo": num2,
            });
            let output = template.render(&globals).unwrap();

            let mut comp = String::new();
            File::open(&output_file)
                .unwrap_or_else(|_| panic!("Expected output file does not exist: {}", output_file))
                .read_to_string(&mut comp)
                .unwrap_or_else(|_| panic!("Failed to read file: {}", output_file));

            assert_diff!(&comp, &output, " ", 0);
        }));
    }

    // Wait for threads to finish
    handles.into_iter().map(|h| h.join()).last();
}
