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

use std::path::Path;

use strum::IntoEnumIterator;
use strum_macros::{Display, EnumIter};

use crate::internal::*;

#[derive(Debug, Display, Clone, PartialEq, EnumIter)]
enum Variant {
    Uefi,
    Baremetal,
}

impl Variant {
    pub fn payload_crate_path(&self) -> &'static str {
        match self {
            Variant::Uefi => "./experimental/uefi/app",
            Variant::Baremetal => "./experimental/uefi/baremetal",
        }
    }

    pub fn loader_mode(&self) -> &'static str {
        match self {
            Variant::Uefi => "uefi",
            Variant::Baremetal => "bios",
        }
    }

    pub fn binary_path(&self) -> &'static str {
        match self {
            Variant::Uefi => {
                "./experimental/uefi/app/target/x86_64-unknown-uefi/debug/uefi-simple.efi"
            }
            Variant::Baremetal => "./experimental/uefi/baremetal/target/target/debug/baremetal",
        }
    }
}

pub fn run_vm_test() -> Step {
    Step::Multiple {
        name: "VM end-to-end test".to_string(),
        steps: Variant::iter().map(run_variant).collect(),
    }
}

fn run_variant(variant: Variant) -> Step {
    Step::Multiple {
        name: format!("run {} variant", variant),
        steps: vec![
            build_binary("build loader binary", "./experimental/uefi/loader"),
            build_binary("build payload", variant.payload_crate_path()),
            Step::WithBackground {
                name: "background loader".to_string(),
                background: run_loader(variant),
                foreground: Box::new(run_client("test")),
            },
        ],
    }
}

fn build_binary(name: &str, directory: &str) -> Step {
    Step::Single {
        name: name.to_string(),
        command: Cmd::new_in_dir("cargo", vec!["build"], Path::new(directory)),
    }
}

fn run_loader(variant: Variant) -> Box<dyn Runnable> {
    Cmd::new(
        "./target/debug/uefi-loader",
        vec![
            format!("--mode={}", variant.loader_mode()),
            variant.binary_path().to_string(),
        ],
    )
}

fn run_client(message: &str) -> Step {
    Step::Multiple {
        name: "build and run client".to_string(),
        steps: vec![
            build_binary("build client binary", "./experimental/uefi/client"),
            Step::Single {
                name: "run client".to_string(),
                command: Cmd::new(
                    "./target/debug/uefi-client",
                    vec!["--request", message, "--expected-response", message],
                ),
            },
        ],
    }
}
