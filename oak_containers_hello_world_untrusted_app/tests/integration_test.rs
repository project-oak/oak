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

//! Integration test that launches the trusted app & invokes it

use clap::Parser;

#[tokio::test]
async fn hello_world() {
    let qemu_path = which::which("qemu-system-x86_64").expect("could not find qemu path");
    let vmm_path_arg = format!(
        "--vmm-binary={}",
        qemu_path.to_str().expect("could not get qemu path as str")
    );
    let arg_strs = [
        "",
        "--port=8080",
        "--system-image=../oak_containers_system_image/target/image.tar.xz",
        "--container-bundle=../oak_containers_hello_world_container/target/oak_container_example_oci_filesystem_bundle.tar",
        &vmm_path_arg,
        "--stage0-binary=../stage0/target/x86_64-unknown-none/release/oak_stage0.bin",
        "--kernel=../oak_containers_kernel/target/vmlinux",
        "--initrd=../target/stage1.cpio",
        "--memory-size=8G",
        "--ramdrive-size=2097152"
    ];
    let launcher_args = oak_containers_launcher::Args::try_parse_from(arg_strs.iter())
        .map_err(|err| err.print())
        .expect("failed to parse args");
    let mut untrusted_app =
        oak_containers_hello_world_untrusted_app::UntrustedApp::create(launcher_args)
            .await
            .expect("could not create untrusted app");
    let greeting = untrusted_app
        .hello("fancy test")
        .await
        .expect("couldn't get greeting");
    assert_eq!(greeting, "Hello from the trusted side, fancy test! Btw, the Trusted App has a config with a length of 0 bytes.")
}
