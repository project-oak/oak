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
    Baremetal,
    Crosvm,
}

impl Variant {
    pub fn payload_crate_path(&self) -> &'static str {
        match self {
            Variant::Baremetal => "./experimental/oak_baremetal_app_qemu",
            Variant::Crosvm => "./experimental/oak_baremetal_app_crosvm",
        }
    }

    pub fn loader_mode(&self) -> &'static str {
        match self {
            Variant::Baremetal => "bios",
            Variant::Crosvm => "crosvm",
        }
    }

    pub fn binary_path(&self) -> &'static str {
        match self {
            Variant::Baremetal => {
                "./experimental/oak_baremetal_app_qemu/target/target/debug/oak_baremetal_app_qemu"
            }
            Variant::Crosvm => {
                "./experimental/oak_baremetal_app_crosvm/target/target/debug/oak_baremetal_app_crosvm"
            }
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
            build_binary("build loader binary", "./experimental/oak_baremetal_loader"),
            build_binary("build payload", variant.payload_crate_path()),
            Step::WithBackground {
                name: "background loader".to_string(),
                background: run_loader(variant),
                foreground: Box::new(run_client("test_key", "^test_value$", 300)),
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
        "./target/debug/oak_baremetal_loader",
        vec![
            format!("--mode={}", variant.loader_mode()),
            variant.binary_path().to_string(),
        ],
    )
}

fn run_client(request: &str, expected_response: &str, iterations: usize) -> Step {
    Step::Multiple {
        name: "build and run client".to_string(),
        steps: vec![
            build_binary("build client binary", "./oak_functions/client/rust"),
            Step::Single {
                name: "run client".to_string(),
                command: Cmd::new(
                    "./target/debug/oak_functions_client",
                    vec![
                        format!("--request={}", request),
                        format!("--expected-response-pattern={}", expected_response),
                        format!("--iterations={}", iterations),
                    ],
                ),
            },
        ],
    }
}
