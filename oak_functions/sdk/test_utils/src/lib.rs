//
// Copyright 2019 The Project Oak Authors
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

//! Test utilities to help with unit testing of Oak-Functions SDK code.

use anyhow::Context;
use log::info;

use std::{path::PathBuf, process::Command};

/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(
    manifest_path: &str,
    module_wasm_file_name: &str,
) -> anyhow::Result<Vec<u8>> {
    let mut module_path = PathBuf::from(manifest_path);
    module_path.pop();
    module_path.push("bin");

    let args = vec![
        // `--out-dir` is unstable and requires `-Zunstable-options`.
        "-Zunstable-options".to_string(),
        "build".to_string(),
        "--release".to_string(),
        "--target=wasm32-unknown-unknown".to_string(),
        format!("--manifest-path={}", manifest_path),
        // Use a fixed target directory, because `--target-dir` influences SHA256 hash
        // of Wasm module.  Target directory should also be synchronized with
        // `--target-dir` used in [`oak_tests::compile_rust_wasm`] in order to have
        // same SHA256 hashes.
        format!("--target-dir={}", {
            let mut target_dir = PathBuf::from(manifest_path);
            target_dir.pop();
            target_dir.push("target");
            target_dir.to_str().expect("Invalid target dir").to_string()
        }),
        format!(
            "--out-dir={}",
            module_path
                .to_str()
                .expect("Invalid target dir")
                .to_string()
        ),
    ];

    Command::new("cargo")
        .args(args)
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("Couldn't spawn cargo build")?
        .wait()
        .context("Couldn't wait for cargo build to finish")?;

    module_path.push(module_wasm_file_name);

    info!("Compiled Wasm module path: {:?}", module_path);

    std::fs::read(module_path).context("Couldn't read compiled module")
}
