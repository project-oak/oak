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

//! This crate allows compiling flatbuffer structs and tables to Rust in `build.rs` scripts.
//!
//! Also see the `oak_idl_gen_services` crate.

use std::process::exit;

/// Compile structs and tables from the provided flatbuffer file using the `flatc` binary
/// installed on the system.
///
/// For an input flatbuffer file with name `test_file.fbs`, the generated Rust file will be located
/// at `${OUT_DIR}/test_file_generated.rs`.
pub fn compile_structs(filename: &str) {
    println!("cargo:rerun-if-changed={}", filename);
    let output = std::process::Command::new("flatc")
        .args(["--rust", "-o", &std::env::var("OUT_DIR").unwrap(), filename])
        .output()
        .unwrap();
    if !output.status.success() {
        eprintln!("flatc exit code: {}", output.status);
        eprintln!(
            "flatc stdout: {}",
            std::str::from_utf8(&output.stdout).unwrap()
        );
        eprintln!(
            "flatc stderr: {}",
            std::str::from_utf8(&output.stderr).unwrap()
        );
        exit(1);
    }
}
