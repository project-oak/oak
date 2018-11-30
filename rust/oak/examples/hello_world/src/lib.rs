//
// Copyright 2018 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

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
