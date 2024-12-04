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

use oak_file_utils::data_path;

pub fn launcher_args(
    container_bundle: impl Into<std::path::PathBuf>,
) -> anyhow::Result<oak_containers_launcher::Args> {
    let container_bundle = container_bundle.into();
    let vmm_binary = which::which("qemu-system-x86_64").expect("could not find qemu path");
    let system_image = data_path("oak_containers/system_image/oak_containers_system_image.tar.xz");
    anyhow::ensure!(system_image.exists(), "System image not found at {system_image:?}");
    let stage0_binary = data_path("stage0_bin/stage0_bin");
    anyhow::ensure!(stage0_binary.exists(), "Stage0 not found at {stage0_binary:?}");
    let kernel = data_path("oak_containers/kernel/bzImage");
    anyhow::ensure!(kernel.exists(), "Kernel not found at {kernel:?}");
    let initrd = data_path("oak_containers/stage1_bin/stage1.cpio");
    anyhow::ensure!(initrd.exists(), "Stage1 not found at {initrd:?}");
    Ok(oak_containers_launcher::Args {
        system_image,
        container_bundle,
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
    })
}
