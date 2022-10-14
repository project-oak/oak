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

use std::{path::PathBuf, process::Command};

const SCHEMA: &str = "schema.fbs";
const TFLITE_SOURCE_DIR: &str = "cc/tflite_micro";
const TFLITE_LIBRARY_NAME: &str = "tflite-micro";

fn main() {
    println!("cargo:rerun-if-changed={}", SCHEMA);
    oak_idl_gen_structs::compile_structs(SCHEMA);
    oak_idl_gen_services::compile_services_servers(SCHEMA);
    // Generate client code for integration tests. These are always built, since
    // we cannot check in this file whether cargo is building for testing or
    // other cases. Ref: https://github.com/rust-lang/cargo/issues/4001
    // As long the generated client code is only used in tests it won't be
    // included in any binaries.
    oak_idl_gen_services::compile_services_clients(SCHEMA);

    build_tflite();
}

/// Builds TensorFlow Lite static library and adds the corresponding build
/// directory to the library search path.
fn build_tflite() {
    // WORKSPACE_ROOT is set in .cargo/config.toml.
    let source_dir: PathBuf = { [env!("WORKSPACE_ROOT"), TFLITE_SOURCE_DIR].iter().collect() };
    // Rerun `build.rs` next time if TensorFlow Lite library sources have been changed.
    println!("cargo:rerun-if-changed={}", source_dir.display());

    let build_target = format!("//{}:{}", TFLITE_SOURCE_DIR, TFLITE_LIBRARY_NAME);
    let status = Command::new("bazel")
        .arg("build")
        .arg(build_target)
        .status()
        .expect("Failed to run bazel build");
    if !status.success() {
        panic!("Failed to run bazel build: exit status is {}", status);
    }

    // Add TensorFlow Lite build directory to the library search path.
    let build_dir: PathBuf = {
        [env!("WORKSPACE_ROOT"), "bazel-bin", TFLITE_SOURCE_DIR]
            .iter()
            .collect()
    };
    println!("cargo:rustc-link-search={}", build_dir.display());
}
