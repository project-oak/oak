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

use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=layout.ld");
    println!("cargo:rustc-link-arg=--script=layout.ld");
    let kernel_directory = "oak_restricted_kernel_bin";
    let file_name = "oak_restricted_kernel_bin";

    let mut kernel_path = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    kernel_path.pop();
    kernel_path.push(kernel_directory);
    let mut source_path = kernel_path.clone();
    source_path.push("target/x86_64-unknown-none/release");
    source_path.push(file_name);
    println!(
        "cargo:rustc-env=PAYLOAD_PATH={}",
        source_path.to_str().unwrap()
    );
}
