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

//! Functionality for testing variants of the baremetal-compatible runtime exposed by the
//! launcher.

const CLIENT_PATH: &str = "./target/debug/oak_functions_client";
const WASM_PATH: &str = "./experimental/oak_baremetal_launcher/key_value_lookup.wasm";
const LOOKUP_PATH: &str = "./experimental/oak_baremetal_launcher/mock_lookup_data";

use std::path::Path;

use strum::IntoEnumIterator;
use strum_macros::{Display, EnumIter};

use crate::internal::*;

#[derive(Debug, Display, Clone, PartialEq, EnumIter)]
pub enum LauncherMode {
    Crosvm,
    Native,
}

impl LauncherMode {
    /// Get the crate name of respective runtime variant
    pub fn runtime_crate_name(&self) -> &'static str {
        match self {
            LauncherMode::Crosvm => "oak_baremetal_app_crosvm",
            LauncherMode::Native => "oak_functions_loader_linux_native",
        }
    }

    /// Get the path to the respective runtime variant that should be launched
    pub fn runtime_crate_path(&self) -> String {
        format!("./experimental/{}", self.runtime_crate_name())
    }

    /// Get the path to the respective runtime variant that should be launched
    pub fn runtime_binary_path(&self) -> String {
        match self {
            LauncherMode::Crosvm => format!(
                "{}/target/x86_64-unknown-none/debug/{}",
                self.runtime_crate_path(),
                self.runtime_crate_name()
            ),
            LauncherMode::Native => format!("./target/debug/{}", self.runtime_crate_name()),
        }
    }

    /// Get the subcommand for launching in this mode
    pub fn variant_subcommand(&self) -> Vec<String> {
        match self {
            LauncherMode::Crosvm => vec![
                "crosvm".to_string(),
                format!("--app-binary={}", &self.runtime_binary_path()),
                format!("--vmm-binary={}", "/usr/local/cargo/bin/crosvm"),
            ],
            LauncherMode::Native => vec![
                "native".to_string(),
                format!("--app-binary={}", &self.runtime_binary_path()),
            ],
        }
    }
}

pub fn run_launcher_test() -> Step {
    Step::Multiple {
        name: "End-to-end tests for the launcher and runtime".to_string(),
        steps: LauncherMode::iter().map(run_variant).collect(),
    }
}

fn run_variant(variant: LauncherMode) -> Step {
    Step::Multiple {
        name: format!("run {} variant", variant),
        steps: vec![
            build_binary(
                "build loader binary",
                "./experimental/oak_baremetal_launcher",
            ),
            build_binary("build runtime", &variant.runtime_crate_path()),
            Step::WithBackground {
                name: "background loader".to_string(),
                background: run_launcher(variant),
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

fn run_launcher(variant: LauncherMode) -> Box<dyn Runnable> {
    let mut args = vec![
        format!("--wasm={}", WASM_PATH),
        format!("--lookup-data={}", LOOKUP_PATH),
    ];
    args.append(&mut variant.variant_subcommand());
    Cmd::new("./target/debug/oak_baremetal_launcher", args)
}

fn run_client(request: &str, expected_response: &str, iterations: usize) -> Step {
    Step::Multiple {
        name: "build and run client".to_string(),
        steps: vec![
            build_binary("build client binary", "./oak_functions/client/rust"),
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
