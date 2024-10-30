//
// Copyright 2024 The Project Oak Authors
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

#[cfg(feature = "bazel")]
const ROOT: &str = "";
#[cfg(not(feature = "bazel"))]
const ROOT: &str = env!("WORKSPACE_ROOT");

pub fn launcher_args(
    container_bundle: impl Into<std::path::PathBuf>,
) -> oak_containers_launcher::Args {
    let system_image = format!("{ROOT}/artifacts/oak_containers_system_image.tar.xz",);
    let vmm_binary = which::which("qemu-system-x86_64").expect("could not find qemu path");
    let stage0_binary = format!("{ROOT}generated/stage0_bin").into();
    let kernel_dir = std::env::var("LINUX_KERNEL")
        .expect("LINUX_KERNEL environment variable should point to the nix-built linux kernel");
    let kernel = format!("{kernel_dir}/bzImage").into();
    let initrd = format!("{ROOT}/target/stage1.cpio").into();
    oak_containers_launcher::Args {
        system_image: system_image.into(),
        container_bundle: container_bundle.into(),
        application_config: Vec::new(),
        qemu_params: oak_containers_launcher::QemuParams {
            vmm_binary,
            stage0_binary,
            kernel,
            initrd,
            memory_size: Some("8G".to_owned()),
            num_cpus: 2,
            ramdrive_size: 3_000_000,
            telnet_console: None,
            virtio_guest_cid: None,
            pci_passthrough: None,
            vm_type: oak_containers_launcher::QemuVmType::Default,
        },
        communication_channel: oak_containers_launcher::ChannelType::default(),
    }
}
