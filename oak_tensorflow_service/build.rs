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

use glob::glob;
use std::{
    path::{Path, PathBuf},
    process::Command,
};

const SCHEMA: &str = "schema.fbs";
const TFLITE_APP_DIR: &str = "cc/tflite_micro/oak/apps/hello_world";
const TFLITE_APP_LIBRARY_NAME: &str = "hello_world_app";
const TFLITE_SOURCES_PATTERN: &str = "cc/tflite_micro/**/*";

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

fn rerun_if_changed<P: AsRef<Path>>(path: P) {
    println!("cargo:rerun-if-changed={}", path.as_ref().display());
}

/// Builds TensorFlow Lite static library and adds the corresponding build
/// directory to the library search path.
fn build_tflite() {
    // WORKSPACE_ROOT is set in .cargo/config.toml.
    // Rerun `build.rs` next time if TensorFlow Lite library sources have been changed.
    let path_pattern = format!("{}/{}", env!("WORKSPACE_ROOT"), TFLITE_SOURCES_PATTERN);
    for entry in glob(&path_pattern).expect("Failed to read tflite source pattern") {
        match entry {
            Ok(path) => rerun_if_changed(&path),
            Err(e) => println!("{:?}", e),
        }
    }

    let build_target = format!("//{}:{}", TFLITE_APP_DIR, TFLITE_APP_LIBRARY_NAME);
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
        [env!("WORKSPACE_ROOT"), "bazel-bin", TFLITE_APP_DIR]
            .iter()
            .collect()
    };
    println!("cargo:rustc-link-search={}", build_dir.display());
}
