extern crate wasm_bindgen;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern {
    fn oak_print(s: &str);
}

#[wasm_bindgen]
pub fn oak_main() {
    oak_print("HELLO OAK");
}
