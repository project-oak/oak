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
//

use std::path::PathBuf;

use anyhow::Context;
use clap::Parser;
use sha2::{Digest, Sha256};
use zerocopy::FromBytes;

/// The default workspace-relative path to the Linux Kernel bzImage file.
const DEFAULT_LINUX_KERNEL: &str = "oak_containers_kernel/target/bzImage";

#[derive(Parser, Clone)]
#[command(about = "Oak Kernel Measurement Calculator")]
struct Cli {
    #[arg(long, help = "The location of the kernel bzImage file")]
    kernel: Option<PathBuf>,
    #[arg(long, help = "The location of output the extracted kernel setup data file to")]
    kernel_setup_data_output: Option<PathBuf>,
    #[arg(long, help = "The location of output the extracted kernel image file to")]
    kernel_image_output: Option<PathBuf>,
}

impl Cli {
    fn kernel_path(&self) -> PathBuf {
        self.kernel.clone().unwrap_or_else(|| {
            format!("{}/{}", env!("WORKSPACE_ROOT"), DEFAULT_LINUX_KERNEL).into()
        })
    }
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let cli = Cli::parse();
    let kernel_info = Kernel::load(cli.kernel_path()).context("couldn't load kernel file")?;
    let mut kernel_hasher = Sha256::new();
    kernel_hasher.update(&kernel_info.kernel_image);
    println!("Kernel Image Measurement: sha2-256:{}", hex::encode(kernel_hasher.finalize()));

    let mut setup_hasher = Sha256::new();
    setup_hasher.update(&kernel_info.setup_data);
    println!("Kernel Setup Data Measurement: sha2-256:{}", hex::encode(setup_hasher.finalize()));

    if let Some(path) = cli.kernel_setup_data_output {
        std::fs::write(path, kernel_info.setup_data).context("couldn't write kernel setup data")?;
    }

    if let Some(path) = cli.kernel_image_output {
        std::fs::write(path, kernel_info.kernel_image).context("couldn't write kernel image")?;
    }

    Ok(())
}

struct Kernel {
    setup_data: Vec<u8>,
    kernel_image: Vec<u8>,
}

impl Kernel {
    /// Parses a bzImage kernel file and extracts the kernel image and setup
    /// data.
    ///
    /// The VMM will parse the the bzImage file and split it into two parts: the
    /// setup data (which includes the real-mode code) and the 64-bit kernel
    /// image. The VMM also updates some fields in the setup data header.
    ///
    /// See <https://github.com/qemu/qemu/blob/6630bc04bccadcf868165ad6bca5a964bb69b067/hw/i386/x86.c#L795>
    /// and <https://www.kernel.org/doc/html/v6.7/arch/x86/boot.html>
    fn from_bz_image(bz_image: &[u8]) -> Self {
        // The number of 512 byte sectors -1 is stored at offset 0x1F1.
        let setup_sects = bz_image[0x1F1];
        // For backwards compatibility, if setup_sects is 0 it should be set to 4.
        let setup_sects = if setup_sects == 0 { 4 } else { setup_sects };
        let setup_size = 512 * (setup_sects as usize + 1);

        // The kernel image is just everything after the setup data.
        let kernel_image = bz_image[setup_size..].to_vec();
        let mut setup_data = bz_image[..setup_size].to_vec();
        // The VMM will modify some fields in the setup data header.
        // The loader type will be set to `QEMU`.
        setup_data[0x210] = 0xB0;
        // The load flags will be updated to enable heap usage.
        setup_data[0x211] |= 0x80;
        // Set the default command_line location.
        let default_cmd_line = 0x20000;
        *u32::mut_from(&mut setup_data[0x228..0x22C]).expect("invalid slice for cmd_line") =
            default_cmd_line;
        // Set the offset to the end of the heap.
        let default_setup = 0x10000;
        *u16::mut_from(&mut setup_data[0x224..0x226]).expect("invalid slice for heap end ptr") =
            (default_cmd_line - default_setup - 0x200) as u16;

        // The location and size of the initial RAM disk will depend on the actual
        // initial RAM disk. To have stable measurements Stage 0 will overwrite
        // these with zeros, before measuring and then overwrite these with the
        // actual values before booting the kernel.
        *u32::mut_from(&mut setup_data[0x218..0x21C]).expect("invalid slice for initrd location") =
            0;
        *u32::mut_from(&mut setup_data[0x21C..0x220]).expect("invalid slice for initrd size") = 0;

        Self { setup_data, kernel_image }
    }

    /// Loads the bzImage-format kernel from the supplied path/
    fn load(kernel_path: PathBuf) -> anyhow::Result<Self> {
        let kernel_bytes = std::fs::read(kernel_path).context("couldn't load kernel bzImage")?;
        log::debug!("Kernel size: {}", kernel_bytes.len());
        let mut hasher = Sha256::new();
        hasher.update(&kernel_bytes);
        log::info!("Kernel digest: sha256:{}", hex::encode(hasher.finalize()));
        Ok(Self::from_bz_image(&kernel_bytes))
    }
}
