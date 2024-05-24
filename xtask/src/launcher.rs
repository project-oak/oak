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

//! Functionality for testing variants of the enclave binary exposed by the
//! launcher.

pub static MOCK_LOOKUP_DATA_PATH: Lazy<PathBuf> =
    Lazy::new(|| workspace_path(&["oak_functions_launcher", "mock_lookup_data"]));
static STAGE_0_DIR: Lazy<PathBuf> = Lazy::new(|| workspace_path(&["stage0_bin"]));
static OAK_FUNCTIONS_LAUNCHER_BIN_DIR: Lazy<PathBuf> =
    Lazy::new(|| workspace_path(&["oak_functions_launcher"]));
static OAK_FUNCTIONS_LAUNCHER_BIN: Lazy<PathBuf> = Lazy::new(|| {
    workspace_path(&["target", "x86_64-unknown-linux-gnu", "debug", "oak_functions_launcher"])
});
pub static OAK_RESTRICTED_KERNEL_WRAPPER_BIN: Lazy<PathBuf> = Lazy::new(|| {
    workspace_path(&[
        "oak_restricted_kernel_wrapper",
        "target",
        "x86_64-unknown-none",
        "release",
        "oak_restricted_kernel_wrapper_bin",
    ])
});
static OAK_RESTRICTED_KERNEL_ORCHESTRATOR: Lazy<PathBuf> = Lazy::new(|| {
    workspace_path(&[
        "enclave_apps",
        "target",
        "x86_64-unknown-none",
        "release",
        "oak_orchestrator",
    ])
});

use std::path::{Path, PathBuf};

use once_cell::sync::Lazy;

use crate::{internal::*, workspace_path};

#[derive(Debug, Clone, PartialEq)]
pub struct App {
    /// app binary crate name.
    crate_name: String,
}

impl App {
    pub fn from_crate_name(crate_name: &str) -> Self {
        Self { crate_name: crate_name.to_string() }
    }

    /// Get the crate name of respective enclave binary variant
    pub fn enclave_crate_name(&self) -> String {
        self.crate_name.clone()
    }

    /// Get the path to the respective enclave binary variant that should be
    /// launched
    pub fn enclave_crate_path(&self) -> String {
        workspace_path(&["enclave_apps", &self.enclave_crate_name()]).to_str().unwrap().to_string()
    }

    /// Get the path to the respective enclave binary variant that should be
    /// launched
    pub fn enclave_binary_path(&self) -> String {
        workspace_path(&[
            "enclave_apps",
            "target",
            "x86_64-unknown-none",
            "debug",
            &self.enclave_crate_name(),
        ])
        .to_str()
        .unwrap()
        .to_string()
    }

    /// Get the subcommand for launching in this mode
    pub fn subcommand(&self) -> Vec<String> {
        vec![
            format!("--kernel={}", OAK_RESTRICTED_KERNEL_WRAPPER_BIN.to_str().unwrap()),
            format!(
                "--vmm-binary={}",
                which::which("qemu-system-x86_64").unwrap().to_str().unwrap()
            ),
            "--memory-size=256M".to_string(),
            format!("--app-binary={}", &self.enclave_binary_path()),
            format!("--initrd={}", OAK_RESTRICTED_KERNEL_ORCHESTRATOR.to_str().unwrap()),
            format!(
                "--bios-binary={}",
                workspace_path(&[
                    "stage0_bin",
                    "target",
                    "x86_64-unknown-none",
                    "release",
                    "oak_stage0.bin",
                ])
                .to_str()
                .unwrap()
            ),
        ]
    }
}

pub fn build_stage0() -> Step {
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
            STAGE_0_DIR.as_path(),
        ),
    }
}

pub fn build_binary(name: &str, directory: &str) -> Step {
    Step::Single {
        name: name.to_string(),
        command: Cmd::new_in_dir("cargo", vec!["build"], Path::new(directory)),
    }
}

pub fn just_build(just_command: &str) -> Step {
    Step::Single {
        name: format!("build {}", just_command),
        command: Cmd::new_in_dir("just", vec![just_command], workspace_path(&[]).as_path()),
    }
}

/// Runs the Oak Functions launcher configured with a default Wasm module for
/// key / value lookups and mock lookup data.
pub fn run_oak_functions_launcher_example(
    app: &App,
    wasm_path: &str,
    port: u16,
) -> Box<dyn Runnable> {
    run_oak_functions_launcher_example_with_lookup_data(
        app,
        wasm_path,
        port,
        MOCK_LOOKUP_DATA_PATH.to_str().unwrap(),
    )
}

pub fn run_oak_functions_launcher_example_with_lookup_data(
    app: &App,
    wasm_path: &str,
    port: u16,
    lookup_data_path: &str,
) -> Box<dyn Runnable> {
    let mut args = vec![
        format!("--wasm={}", wasm_path),
        format!("--port={}", port),
        format!("--lookup-data={}", lookup_data_path),
    ];
    args.append(&mut app.subcommand());
    Cmd::new(OAK_FUNCTIONS_LAUNCHER_BIN.to_str().unwrap(), args)
}

pub fn run_launcher(launcher_bin: &str, app: &App) -> Box<dyn Runnable> {
    let mut args = vec![];
    args.append(&mut app.subcommand());
    Cmd::new(launcher_bin, args)
}

/// Runs the specified example as a background task. Returns a reference to the
/// running server and the port on which the server is listening.
pub async fn run_oak_functions_example_in_background(
    wasm_path: &str,
    lookup_data_path: &str,
) -> (crate::testing::BackgroundStep, u16) {
    crate::testing::run_step(crate::launcher::build_stage0()).await;
    crate::testing::run_step(crate::launcher::just_build("oak_restricted_kernel_wrapper")).await;
    crate::testing::run_step(crate::launcher::just_build("oak_orchestrator")).await;
    crate::testing::run_step(crate::launcher::build_binary(
        "build Oak Functions Launcher binary",
        crate::launcher::OAK_FUNCTIONS_LAUNCHER_BIN_DIR.to_str().unwrap(),
    ))
    .await;
    let variant = crate::launcher::App::from_crate_name("oak_functions_enclave_app");
    crate::testing::run_step(crate::launcher::build_binary(
        "build Oak Functions enclave app",
        &variant.enclave_crate_path(),
    ))
    .await;

    eprintln!("using Wasm module {}", wasm_path);

    let port = portpicker::pick_unused_port().expect("failed to pick a port");
    eprintln!("using port {}", port);

    let background = crate::testing::run_background(
        crate::launcher::run_oak_functions_launcher_example_with_lookup_data(
            &variant,
            wasm_path,
            port,
            lookup_data_path,
        ),
    )
    .await;

    (background, port)
}
