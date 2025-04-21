//
// Copyright 2025 The Project Oak Authors
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

#[cxx::bridge(namespace = "oak::private_memory")]
mod ffi {
    // C++ types and signatures exposed to Rust.
    unsafe extern "C++" {
        include!("src/cxx_example/mystring.h");

        type MyString;

        unsafe fn new_cxx_string(buffer: *const u8, len: usize) -> UniquePtr<MyString>;
        fn len(&self) -> usize;
    }
}

use crate::ffi::new_cxx_string;

fn main() {
    let string = "This is a string";
    let my_str = unsafe { new_cxx_string(string.as_ptr() as *const u8, string.len()) };
    assert_eq!(my_str.len(), string.len());
}
