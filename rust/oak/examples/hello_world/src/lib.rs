extern crate oak;
extern crate wasm_bindgen;

use std::io::Read;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn oak_main() {
    oak::print("HELLO OAK\n");

    let t = oak::get_time();
    oak::print(&format!("Time: {:?}\n", t));

    let mut in1 = oak::get_input(0);
    let mut buf = [0; 10];
    in1.read(&mut buf);
    let s = std::str::from_utf8(&buf).unwrap();
    oak::print(&format!("Val: {}\n", s));
}
