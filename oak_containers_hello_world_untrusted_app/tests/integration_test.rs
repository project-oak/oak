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

//! Integration test that launches the trusted app and invokes it.

use clap::Parser;
use oak_containers_launcher::Args;
use std::sync::Once;

static INIT: Once = Once::new();

fn init_logging() {
    INIT.call_once(|| {
        env_logger::init();
    });
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn hello_world() {
    init_logging();

    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    // This takes a long time, but we want to make sure everything it up to date.
    // TODO(#4195): Stop dependencies from always being rebuilt.
    build_dependencies().expect("couldn't build dependencies");

    let mut untrusted_app =
        oak_containers_hello_world_untrusted_app::UntrustedApp::create(get_laucnher_args())
            .await
            .expect("could not create untrusted app");
    let greeting = untrusted_app
        .hello("fancy test")
        .await
        .expect("couldn't get greeting");

    untrusted_app.kill().await;

    log::info!("Greeting: {}", greeting);
    assert_eq!(greeting, "Hello from the trusted side, fancy test! Btw, the Trusted App has a config with a length of 0 bytes.");
}

fn build_dependencies() -> anyhow::Result<()> {
    duct::cmd!("just", "all_oak_containers_binaries",)
        .dir(env!("WORKSPACE_ROOT"))
        .run()?;
    Ok(())
}

fn get_laucnher_args() -> Args {
    let qemu_path = which::which("qemu-system-x86_64").expect("could not find qemu path");
    let vmm_path_arg = format!(
        "--vmm-binary={}",
        qemu_path.to_str().expect("could not get qemu path as str")
    );
    let system_image_arg = format!(
        "--system-image={}oak_containers_system_image/target/image.tar.xz",
        env!("WORKSPACE_ROOT")
    );
    let container_bundle_arg = format!(
        "--container-bundle={}oak_containers_hello_world_container/target/oak_container_example_oci_filesystem_bundle.tar",
        env!("WORKSPACE_ROOT")
    );
    let stage0_binary_arg = format!(
        "--stage0-binary={}stage0_bin/target/x86_64-unknown-none/release/stage0_bin",
        env!("WORKSPACE_ROOT")
    );
    let kernel_arg = format!(
        "--kernel={}oak_containers_kernel/target/bzImage",
        env!("WORKSPACE_ROOT")
    );
    let initrd_arg = format!("--initrd={}/target/stage1.cpio", env!("WORKSPACE_ROOT"));
    let arg_strs = [
        "",
        "--port=8080",
        &system_image_arg,
        &container_bundle_arg,
        &vmm_path_arg,
        &stage0_binary_arg,
        &kernel_arg,
        &initrd_arg,
        "--memory-size=8G",
        "--ramdrive-size=3000000",
    ];
    Args::try_parse_from(arg_strs.iter())
        .map_err(|err| err.print())
        .expect("failed to parse args")
}
