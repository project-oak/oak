//
// Copyright 2023 The Project Oak Authors
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

use std::{
    fs::{copy, File},
    io::Write,
    path::PathBuf,
};

fn main() {
    println!("cargo:rerun-if-changed=layout.ld");
    println!("cargo:rustc-link-arg=--script=layout.ld");
    let kernel_directory = "oak_restricted_kernel_bin";
    let file_name = "oak_restricted_kernel_bin";

    // The source file is the output from building "../oak_restricted_kernel_bin" in release mode.
    let mut source_path = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    source_path.pop();
    source_path.push(kernel_directory);
    source_path.push("target/x86_64-unknown-none/release");
    source_path.push(file_name);
    let mut destination_path = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    destination_path.push(file_name);
    if destination_path.exists() {
        copy(&source_path, &destination_path).unwrap();
    } else {
        // Create a fake file so cargo clippy doesn't break if the kernel was not built.
        File::create(&destination_path)
            .unwrap()
            .write_all(b"invalid")
            .unwrap();
    }

    println!(
        "cargo:rustc-env=PAYLOAD_PATH={}",
        destination_path.to_str().unwrap()
    );
}
