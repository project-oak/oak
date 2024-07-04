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
pub static OAK_RESTRICTED_KERNEL_WRAPPER_BIN: Lazy<PathBuf> = Lazy::new(|| {
    workspace_path(&[
        "oak_restricted_kernel_wrapper",
        "target",
        "x86_64-unknown-none",
        "release",
        "oak_restricted_kernel_wrapper_bin",
    ])
});

use std::path::PathBuf;

use once_cell::sync::Lazy;

use crate::{internal::*, workspace_path};

pub fn run_oak_functions_launcher_example_with_lookup_data(
    wasm_path: &str,
    port: u16,
    lookup_data_path: &str,
) -> Box<dyn Runnable> {
    Cmd::new(
        "just",
        vec!["run_oak_functions_launcher", wasm_path, &format!("{port}"), lookup_data_path],
    )
}

/// Runs the specified example as a background task. Returns a reference to the
/// running server and the port on which the server is listening.
pub async fn run_oak_functions_example_in_background(
    wasm_path: &str,
    lookup_data_path: &str,
) -> (crate::testing::BackgroundStep, u16) {
    eprintln!("using Wasm module {}", wasm_path);

    let port = portpicker::pick_unused_port().expect("failed to pick a port");
    eprintln!("using port {}", port);

    let background = crate::testing::run_background(
        crate::launcher::run_oak_functions_launcher_example_with_lookup_data(
            wasm_path,
            port,
            lookup_data_path,
        ),
    )
    .await;

    (background, port)
}
