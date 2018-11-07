extern crate wasm_bindgen;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern {
    fn oak_print(s: &str);
    fn oak_get_time() -> i32;
}

#[wasm_bindgen]
pub fn oak_main() {
    oak_print("HELLO OAK");
}
