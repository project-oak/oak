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

use std::io::Read;

#[no_mangle]
pub extern "C" fn oak_initialize() {
    oak::print("Oak initialize\n");
}

#[no_mangle]
pub extern "C" fn oak_finalize() {
    oak::print("Oak finalize\n");
}

#[no_mangle]
pub extern "C" fn oak_invoke() {
    oak::print("Oak invoke\n");

    oak::print("HELLO OAK\n");

    let t = oak::get_time();
    oak::print(&format!("Time: {:?}\n", t));

    let mut in1 = oak::get_input();
    let mut s = String::new();
    in1.read_to_string(&mut s).expect("could not read string");
    oak::print(&format!("Val: {}\n", s));
}
