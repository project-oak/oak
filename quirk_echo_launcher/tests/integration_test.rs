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

//! Integration tests for the Quirk Echo Launcher.

use std::time::Duration;

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    xtask::testing::run_step(xtask::launcher::build_stage0()).await;
    xtask::testing::run_step(xtask::launcher::build_binary(
        "build Oak Restricted Kernel binary",
        xtask::launcher::OAK_RESTRICTED_KERNEL_BIN_DIR
            .to_str()
            .unwrap(),
    ))
    .await;
    let app = xtask::launcher::App::from_crate_name("quirk_echo_enclave_app");
    xtask::testing::run_step(xtask::launcher::build_binary(
        "build Quirk Echo enclave app",
        &app.enclave_crate_path(),
    ))
    .await;

    let _background = xtask::testing::run_background(xtask::launcher::run_launcher(
        xtask::launcher::QUIRK_ECHO_LAUNCHER_BIN.to_str().unwrap(),
        &app,
    ))
    .await;

    // Wait for the server to start up.
    // Currently the Quirk Echo Launcher does not expose a gRPC service, it just invokes a method on
    // the Enclave application directly and then immediately terminates.
    tokio::time::sleep(Duration::from_secs(5)).await;
}
