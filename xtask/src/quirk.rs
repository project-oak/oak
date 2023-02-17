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

use crate::{internal::*, launcher::*};

fn run_variant(variant: &LauncherMode) -> Step {
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
        LauncherMode::Virtual(_) => vec![
            build_stage0(),
            build_binary(
                "build Restricted Kernel binary",
                "oak_restricted_kernel_bin",
            ),
        ],
        LauncherMode::Native(_) => panic!("not supported"),
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

fn run_launcher(variant: &LauncherMode) -> Box<dyn Runnable> {
    let args = variant.variant_subcommand();
    Cmd::new("./target/debug/quirk_echo_launcher", args)
}

pub fn run_launcher_test() -> Step {
    let mut steps = vec![build_binary(
        "build Quirk Echo launcher",
        "./quirk_echo_launcher",
    )];
    let virt = LauncherMode::Virtual("quirk_echo_enclave_app".to_string());
    steps.push(run_variant(&virt));

    Step::Multiple {
        name: "End-to-end tests for the launcher and enclave binary".to_string(),
        steps,
    }
}
