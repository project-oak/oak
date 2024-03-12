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

use crate::{
    internal::{Cmd, Runnable, Step},
    workspace_path,
};

fn build_kernel() -> Step {
    Step::Single {
        name: "build kernel".to_string(),
        command: Cmd::new("just", vec!["oak_containers_kernel"]),
    }
}

fn build_stage1() -> Step {
    Step::Single {
        name: "build stage1".to_string(),
        command: Cmd::new("just", vec!["stage1_cpio"]),
    }
}

fn build_system_image() -> Step {
    Step::Single {
        name: "build system image".to_string(),
        command: Cmd::new("just", vec!["oak_containers_system_image"]),
    }
}

fn build_oak_functions_bundle() -> Step {
    Step::Single {
        name: "build Oak Functions bundle".to_string(),
        command: Cmd::new(
            "just",
            vec!["oak_functions_containers_container_bundle_tar"],
        ),
    }
}

fn build_oak_functions_launcher() -> Step {
    Step::Single {
        name: "build Oak Functions bundle".to_string(),
        command: Cmd::new("just", vec!["oak_functions_containers_launcher"]),
    }
}

async fn build_prerequisites() {
    // `just` steps can clash with each other, so ensure that we're not trying to build things like
    // the system image concurrently.
    static BUILD: tokio::sync::OnceCell<()> = tokio::sync::OnceCell::const_new();
    BUILD
        .get_or_init(async || {
            tokio::join!(
                crate::testing::run_step(crate::launcher::build_stage0()),
                crate::testing::run_step(build_kernel()),
                crate::testing::run_step(build_stage1()),
                crate::testing::run_step(build_system_image()),
                crate::testing::run_step(build_oak_functions_bundle()),
                crate::testing::run_step(build_oak_functions_launcher())
            );
        })
        .await;
}

pub fn run_oak_functions_launcher_example_with_lookup_data(
    wasm_path: &str,
    port: u16,
    lookup_data_path: &str,
    communication_channel: &str,
) -> Box<dyn Runnable> {
    let args = vec![
        format!(
            "--vmm-binary={}",
            which::which("qemu-system-x86_64")
                .unwrap()
                .to_str()
                .unwrap()
        ),
        format!(
            "--stage0-binary={}",
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
        format!(
            "--kernel={}",
            workspace_path(&["oak_containers_kernel", "target", "bzImage"])
                .to_str()
                .unwrap()
        ),
        format!(
            "--initrd={}",
            workspace_path(&["target", "stage1.cpio"]).to_str().unwrap()
        ),
        format!(
            "--system-image={}",
            workspace_path(&["oak_containers_system_image", "target", "image.tar.xz"])
                .to_str()
                .unwrap()
        ),
        format!(
            "--container-bundle={}",
            workspace_path(&[
                "oak_functions_containers_container",
                "target",
                "oak_functions_container_oci_filesystem_bundle.tar",
            ])
            .to_str()
            .unwrap()
        ),
        format!("--ramdrive-size={}", "1000000"), // 1 GiB in KiB
        format!("--memory-size={}", "2G"),
        format!("--wasm={}", wasm_path),
        format!("--port={}", port),
        format!("--lookup-data={}", lookup_data_path),
        // Use the current thread ID as the CID, as we may have tests that start multiple QEMUs in
        // parallel. Starting multiple QEMUs in one thread will fail.
        format!("--virtio-guest-cid={}", nix::unistd::gettid()),
        format!("--communication-channel={}", communication_channel),
    ];
    Cmd::new(
        workspace_path(&[
            "target",
            "x86_64-unknown-linux-gnu",
            "release",
            "oak_functions_containers_launcher",
        ])
        .to_str()
        .unwrap(),
        args,
    )
}

/// Runs the specified example as a background task. Returns a reference to the running server and
/// the port on which the server is listening.
pub async fn run_oak_functions_example_in_background(
    wasm_path: &str,
    lookup_data_path: &str,
    communication_channel: &str,
) -> (crate::testing::BackgroundStep, u16) {
    build_prerequisites().await;

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
