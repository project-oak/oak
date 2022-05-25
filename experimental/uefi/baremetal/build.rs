//
// Copyright 2022 The Project Oak Authors
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

extern crate bindgen;

use std::{env, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=target.json");
    println!("cargo:rerun-if-changed=layout.ld");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());

    // We need to override the target as our default target is our own custom target, which is not
    // recognized by clang.
    let bindings = bindgen::Builder::default()
        .clang_arg("--target=x86_64-pc-linux-gnu")
        .header("src/hvm_start_info.h")
        .allowlist_type("hvm_start_info")
        .allowlist_type("hvm_memmap_table_entry")
        .blocklist_type("__uint32_t")
        .blocklist_type("__uint64_t")
        .layout_tests(false)
        .generate()
        .unwrap();
    bindings
        .write_to_file(out_path.join("start_info.rs"))
        .unwrap();
}
