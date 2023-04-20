//
// Copyright 2021 The Project Oak Authors
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

use crate::{
    internal::*,
    launcher::{
        build_binary, build_stage0, run_oak_functions_launcher_example_with_lookup_data,
        LauncherMode, MOCK_LOOKUP_DATA_PATH, OAK_RESTRICTED_KERNEL_BIN_DIR,
    },
};

/// Build the Rust crate that will be used as the Wasm module for the Oak Functions server.
pub fn build_rust_crate_wasm(crate_name: &str) -> Step {
    Step::Single {
        name: "cargo build Wasm".to_string(),
        command: Cmd::new(
            "cargo",
            vec![
                "build".to_string(),
                "--target=wasm32-unknown-unknown".to_string(),
                "--release".to_string(),
                format!("--package={crate_name}"),
            ],
        ),
    }
}

pub fn run_oak_functions_example(opt: &RunOakExampleOpt) -> Step {
    let variant = LauncherMode::Virtual("oak_functions_enclave_app".to_string());

    let wasm_path = oak_functions_test_utils::rust_crate_wasm_out_path(&opt.example_name);

    Step::Multiple {
        name: "run Oak Functions example".to_string(),
        steps: vec![
            build_stage0(),
            build_binary(
                "build Oak Restricted Kernel binary",
                OAK_RESTRICTED_KERNEL_BIN_DIR.to_str().unwrap(),
            ),
            build_binary(
                "build Oak Functions enclave app",
                &variant.enclave_crate_path(),
            ),
            build_rust_crate_wasm(&opt.example_name),
            Step::Single {
                name: "server".to_string(),
                command: run_oak_functions_launcher_example_with_lookup_data(
                    &variant,
                    &wasm_path,
                    8080,
                    &opt.lookup_data_path
                        .clone()
                        .unwrap_or(MOCK_LOOKUP_DATA_PATH.to_str().unwrap().to_string()),
                ),
            },
        ],
    }
}
