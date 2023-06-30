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
    path::{Path, PathBuf},
    process::Command,
    str::from_utf8,
};

const LIBRARY_DIR: &str = "cc/iree";
const LIBRARY_NAME: &str = "iree";
const LIBRARY_DEPENDENCIES_DIR: &str = "/workspace/cc/iree";
// TODO(#3864): Use Oak Toolchain to compile the library.
// In order to compile with internally built IREE library - uncomment the following line.
// const LIBRARY_DEPENDENCIES: [&str; 2] = ["c", "gloss"];
const LIBRARY_DEPENDENCIES: [&str; 0] = [];

fn main() {
    micro_rpc_build::compile(
        &[format!(
            "{}oak_iree_service/proto/oak_iree.proto",
            env!("WORKSPACE_ROOT")
        )],
        &[format!("{}oak_iree_service/proto", env!("WORKSPACE_ROOT"))],
    );

    build_library();

    // Link `newlib` to the library.
    // TODO(#3864): Use Oak Toolchain to compile the library.
    println!("cargo:rustc-link-search={}", LIBRARY_DEPENDENCIES_DIR);
    for dependency in LIBRARY_DEPENDENCIES {
        rustc_link_lib(dependency);
    }
}

/// Builds a static library and adds the corresponding build
/// directory to the library search path.
fn build_library() {
    // Build library.
    let build_dir = build_bazel_target(LIBRARY_DIR, LIBRARY_NAME);

    // Add build directory to the library search path.
    println!("cargo:rustc-link-search={}", build_dir.display());
}

/// Builds Bazel `target` and makes `build.rs` rerun next time if one of the dependencies have been
/// updated.
fn build_bazel_target(target_dir: &str, target: &str) -> PathBuf {
    // Get dependency file paths.
    let build_target = format!("//{}:{}", target_dir, target);
    let bazel_query = format!("kind('source file', deps({}))", build_target);
    let output = Command::new("bazel")
        .arg("query")
        .arg(bazel_query)
        .output()
        .expect("couldn't run bazel query");
    if !output.status.success() {
        panic!("couldn't run bazel query: exit status is {}", output.status);
    }
    let dependency_paths = from_utf8(&output.stdout)
        .expect("couldn't parse bazel query output")
        .split('\n')
        .filter_map(build_target_to_path)
        .collect::<Vec<_>>();

    // Rerun `build.rs` next time one of the dependencies has been updated.
    for path in dependency_paths {
        rerun_if_changed(&path);
    }

    // Build Bazel target.
    let status = Command::new("bazel")
        .arg("build")
        .arg(build_target)
        .status()
        .expect("couldn't run bazel build");
    if !status.success() {
        panic!("couldn't run bazel build: exit status is {}", status);
    }

    // WORKSPACE_ROOT is set in .cargo/config.toml.
    return [env!("WORKSPACE_ROOT"), "bazel-bin", target_dir]
        .iter()
        .collect();
}

fn build_target_to_path(target: &str) -> Option<PathBuf> {
    if target.starts_with('@') {
        None
    } else {
        let file_path = target
            .split("//")
            .last()
            .expect("couldn't remove bazel build target prefix")
            .replace(':', "/");
        if file_path.is_empty() {
            None
        } else {
            Some([env!("WORKSPACE_ROOT"), &file_path].iter().collect())
        }
    }
}

fn rerun_if_changed<P: AsRef<Path>>(path: P) {
    println!("cargo:rerun-if-changed={}", path.as_ref().display());
}

fn rustc_link_lib<P: AsRef<Path>>(path: P) {
    println!("cargo:rustc-link-lib=static={}", path.as_ref().display());
}
