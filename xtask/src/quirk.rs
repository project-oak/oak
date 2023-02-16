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

//! Functionality for testing variants of the enclave binary exposed by the launcher.

use crate::internal::*;
use std::path::Path;
use strum::IntoEnumIterator;
use strum_macros::{Display, EnumIter};

#[derive(Debug, Display, Copy, Clone, PartialEq, EnumIter)]
pub enum LauncherMode {
    Virtualized,
}

impl LauncherMode {
    /// Get the crate name of respective enclave binary variant
    pub fn enclave_crate_name(&self) -> &'static str {
        match self {
            LauncherMode::Virtualized => "quirk_echo_enclave_app",
        }
    }

    /// Get the path to the respective enclave binary variant that should be launched
    pub fn enclave_crate_path(&self) -> String {
        format!("./{}", self.enclave_crate_name())
    }

    /// Get the path to the respective enclave binary variant that should be launched
    pub fn enclave_binary_path(&self) -> String {
        match self {
            LauncherMode::Virtualized => format!(
                "{}/target/x86_64-unknown-none/debug/{}",
                self.enclave_crate_path(),
                self.enclave_crate_name()
            ),
        }
    }

    /// Get the subcommand for launching in this mode
    pub fn variant_subcommand(&self) -> Vec<String> {
        match self {
            LauncherMode::Virtualized => vec![
                "virtualized".to_string(),
                format!(
                    "--enclave-binary={}",
                    "./oak_restricted_kernel_bin/target/x86_64-unknown-none/debug/oak_restricted_kernel_bin"
                ),
                format!("--vmm-binary={}", "/usr/bin/qemu-system-x86_64"),
                format!("--app-binary={}", &self.enclave_binary_path()),
                format!(
                    "--bios-binary={}",
                    "./stage0/target/x86_64-unknown-none/release/oak_stage0.bin"
                ),
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
            LauncherMode::Virtualized => var == "virtualized",
        },
    }
}

fn build_released_binary(name: &str, directory: &str) -> Step {
    Step::Single {
        name: name.to_string(),
        command: Cmd::new_in_dir("cargo", vec!["build", "--release"], Path::new(directory)),
    }
}

fn run_variant(variant: LauncherMode) -> Step {
    let mut steps = vec![build_binary(
        "build Quirk Echo enclave binary",
        &variant.enclave_crate_path(),
    )];
    // If we want to run in an VMM, we need three binaries:
    // 1. the stage0 BIOS image,
    // 2. the kernel binary,
    // 3. the actual Quirk Echo enclave application.
    // (1) and (2) are needed to start the VMM, and the kernel expects to read (3) as the very first
    // thing over the communication channel.
    steps.extend(match variant {
        LauncherMode::Virtualized => vec![
            build_stage0(),
            build_binary(
                "build Restricted Kernel binary",
                "oak_restricted_kernel_bin",
            ),
        ],
    });
    steps.push(Step::WithBackground {
        name: "background launcher".to_string(),
        background: run_launcher(variant),
        foreground: Box::new(Step::Single {
            name: "waiting for 10 seconds".to_string(),
            command: Cmd::new("sleep", ["10"]),
        }),
    });
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
    let args = variant.variant_subcommand();
    Cmd::new("./target/debug/quirk_echo_launcher", args)
}

pub fn run_launcher_test() -> Step {
    let mut steps = vec![build_binary(
        "build Quirk Echo launcher",
        "./quirk_echo_launcher",
    )];
    steps.extend(LauncherMode::iter().map(run_variant));

    Step::Multiple {
        name: "End-to-end tests for the launcher and enclave binary".to_string(),
        steps,
    }
}
