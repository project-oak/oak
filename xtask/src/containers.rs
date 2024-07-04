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

use crate::internal::{Cmd, Runnable};

pub fn run_oak_functions_launcher_example_with_lookup_data(
    wasm_path: &str,
    port: u16,
    lookup_data_path: &str,
    communication_channel: &str,
) -> Box<dyn Runnable> {
    Cmd::new(
        "just",
        vec![
            "run_oak_functions_containers_launcher",
            wasm_path,
            &format!("{}", port),
            lookup_data_path,
            communication_channel,
            &format!("{}", nix::unistd::gettid()),
        ],
    )
}

/// Runs the specified example as a background task. Returns a reference to the
/// running server and the port on which the server is listening.
pub async fn run_oak_functions_example_in_background(
    wasm_path: &str,
    lookup_data_path: &str,
    communication_channel: &str,
) -> (crate::testing::BackgroundStep, u16) {
    eprintln!("using Wasm module {}", wasm_path);

    let port = portpicker::pick_unused_port().expect("failed to pick a port");
    eprintln!("using port {}", port);

    let background =
        crate::testing::run_background(run_oak_functions_launcher_example_with_lookup_data(
            wasm_path,
            port,
            lookup_data_path,
            communication_channel,
        ))
        .await;

    (background, port)
}
