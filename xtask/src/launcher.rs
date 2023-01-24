//
// Copyright 2020 The Project Oak Authors
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

//! Functionality for testing variants of the enclave binary exposed by the launcher.

const CLIENT_PATH: &str = "./target/debug/oak_functions_client";
const WASM_PATH: &str = "./oak_functions_launcher/key_value_lookup.wasm";
const LOOKUP_PATH: &str = "./oak_functions_launcher/mock_lookup_data";

use crate::internal::*;
use std::path::Path;
use strum::IntoEnumIterator;
use strum_macros::{Display, EnumIter};

#[derive(Debug, Display, Copy, Clone, PartialEq, EnumIter)]
pub enum LauncherMode {
    Virtual,
    Native,
}

impl LauncherMode {
    /// Get the crate name of respective enclave binary variant
    pub fn enclave_crate_name(&self) -> &'static str {
        match self {
            LauncherMode::Virtual => "oak_functions_app",
            LauncherMode::Native => "oak_functions_linux_fd_bin",
        }
    }

    /// Get the path to the respective enclave binary variant that should be launched
    pub fn enclave_crate_path(&self) -> String {
        format!("./{}", self.enclave_crate_name())
    }

    /// Get the path to the respective enclave binary variant that should be launched
    pub fn enclave_binary_path(&self) -> String {
        match self {
            LauncherMode::Virtual => format!(
                "{}/target/x86_64-unknown-none/debug/{}",
                self.enclave_crate_path(),
                self.enclave_crate_name()
            ),
            LauncherMode::Native => format!("./target/debug/{}", self.enclave_crate_name()),
        }
    }

    /// Get the subcommand for launching in this mode
    pub fn variant_subcommand(&self) -> Vec<String> {
        match self {
            LauncherMode::Virtual => vec![
                "virtual".to_string(),
                format!(
                    "--enclave-binary={}",
                    "./oak_enclave_shim/target/x86_64-unknown-none/debug/oak_enclave_shim"
                ),
                format!("--vmm-binary={}", "/usr/bin/qemu-system-x86_64"),
                format!("--app-binary={}", &self.enclave_binary_path()),
                format!(
                    "--bios-binary={}",
                    "./stage0/target/x86_64-unknown-none/release/oak_stage0.bin"
                ),
            ],
            LauncherMode::Native => vec![
                "native".to_string(),
                format!("--enclave-binary={}", &self.enclave_binary_path()),
            ],
        }
    }
}

pub fn build_enclave_binary_variants(opt: &BuildEnclaveBinaryVariantsOpt) -> Step {
    Step::Multiple {
        name: "Build enclave binary variants".to_string(),
        steps: LauncherMode::iter()
            .filter(|v| option_covers_variant(opt, v))
            .map(|v| build_released_binary(&v.to_string(), &v.enclave_crate_path()))
            .collect(),
    }
}

fn option_covers_variant(opt: &BuildEnclaveBinaryVariantsOpt, variant: &LauncherMode) -> bool {
    match &opt.variant {
        None => true,
        Some(var) => match *variant {
            LauncherMode::Native => var == "native",
            LauncherMode::Virtual => var == "virtual",
        },
    }
}

fn build_released_binary(name: &str, directory: &str) -> Step {
    Step::Single {
        name: name.to_string(),
        command: Cmd::new_in_dir("cargo", vec!["build", "--release"], Path::new(directory)),
    }
}

pub fn run_launcher_test() -> Step {
    let mut steps = vec![build_binary(
        "build Oak Functions launcher",
        "./oak_functions_launcher",
    )];
    steps.extend(LauncherMode::iter().map(run_variant));

    Step::Multiple {
        name: "End-to-end tests for the launcher and enclave binary".to_string(),
        steps,
    }
}

fn run_variant(variant: LauncherMode) -> Step {
    let mut steps = vec![build_binary(
        "build Oak Functions enclave binary",
        &variant.enclave_crate_path(),
    )];
    // If we want to run in an VMM, we need three binaries:
    // 1. the stage0 BIOS image,
    // 2. the kernel binary,
    // 3. the actual Oak Functions enclave application.
    // (1) and (2) are needed to start the VMM, and the kernel expects to read (3) as the very first
    // thing over the communication channel.
    steps.extend(match variant {
        LauncherMode::Virtual => vec![
            build_stage0(),
            build_binary(
                "build Restricted Kernel binary",
                "oak_restricted_kernel_bin",
            ),
        ],
        LauncherMode::Native => vec![],
    });
    steps.extend(vec![Step::WithBackground {
        name: "background launcher".to_string(),
        background: run_launcher(variant),
        foreground: Box::new(run_client("test_key", "^test_value$", 300)),
    }]);
    Step::Multiple {
        name: format!("run {} variant", variant),
        steps,
    }
}

fn build_stage0() -> Step {
    Step::Single {
        name: "build stage0".to_string(),
        command: Cmd::new_in_dir(
            "cargo",
            vec![
                "objcopy",
                "--release",
                "--",
                "-O",
                "binary",
                "target/x86_64-unknown-none/release/oak_stage0.bin",
            ],
            Path::new("./stage0"),
        ),
    }
}

fn build_binary(name: &str, directory: &str) -> Step {
    Step::Single {
        name: name.to_string(),
        command: Cmd::new_in_dir("cargo", vec!["build"], Path::new(directory)),
    }
}

fn run_launcher(variant: LauncherMode) -> Box<dyn Runnable> {
    let mut args = vec![
        format!("--wasm={}", WASM_PATH),
        format!("--lookup-data={}", LOOKUP_PATH),
    ];
    args.append(&mut variant.variant_subcommand());
    Cmd::new("./target/debug/oak_functions_launcher", args)
}

fn run_client(request: &str, expected_response: &str, iterations: usize) -> Step {
    Step::Multiple {
        name: "build and run client".to_string(),
        steps: vec![
            build_binary("build client binary", "./oak_functions_client"),
            Step::Single {
                name: "run client".to_string(),
                command: Cmd::new(
                    CLIENT_PATH,
                    vec![
                        format!("--request={}", request),
                        format!("--expected-response-pattern={}", expected_response),
                        format!("--iterations={}", iterations),
                    ],
                ),
            },
            Step::Single {
                name: "run client with a large message".to_string(),
                command: Cmd::new(CLIENT_PATH, vec!["--test-large-message"]),
            },
        ],
    }
}
