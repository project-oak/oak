extern crate oak;
extern crate wasm_bindgen;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn oak_main() {
    let t = oak::get_time();
    oak::print(&format!("HELLO OAK {:?}", t));
}
