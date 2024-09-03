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

use alloc::{ffi::CString, string::String, vec};
use core::slice;

use x86_64::{PhysAddr, VirtAddr};

use crate::{fw_cfg::FwCfg, Measured};

/// The default location for loading a compressed (bzImage format) kerne.
const DEFAULT_BZIMAGE_START: u64 = 0x2000000; // See b/359144829 before changing.

/// Information about the kernel image.
pub struct KernelInfo {
    /// The start address where the kernel is loaded.
    pub start_address: VirtAddr,
    /// The size of the kernel image.
    pub size: usize,
    /// The entry point for the kernel.
    pub entry: VirtAddr,
    /// The SHA2-256 digest of the raw kernel image.
    pub measurement: crate::Measurement,
}

/// Tries to load the kernel command-line from the fw_cfg device.
///
/// We first try to read it using the traditional selector. If it is not
/// available there we try to read it using a custom file path.
pub fn try_load_cmdline<P: crate::Platform>(fw_cfg: &mut FwCfg<P>) -> Option<String> {
    let cmdline_file = fw_cfg.get_cmdline_file()?;
    // Safety: len will always be at least 1 byte, and we don't care about
    // alignment. If the allocation fails, we won't try coercing it into a
    // slice.
    let mut buf = vec![0u8; cmdline_file.size()];
    let actual_size = fw_cfg.read_file(&cmdline_file, &mut buf).expect("could not read cmdline");
    assert_eq!(actual_size, cmdline_file.size(), "cmdline size did not match expected size");

    let cmdline = CString::from_vec_with_nul(buf)
        .expect("invalid kernel command-line")
        .into_string()
        .expect("invalid kernel command-line");
    log::debug!("Kernel cmdline: {}", cmdline);
    Some(cmdline)
}

/// Tries to load a kernel image from the QEMU fw_cfg device.
///
/// We assume that a kernel file provided via the traditional selector is a
/// compressed kernel using the bzImage format. We assume that a kernel file
/// provided via the custom filename of "opt/stage0/elf_kernel" is an
/// uncompressed ELF file.
///
/// If it finds a kernel it returns the information about the kernel, otherwise
/// `None`.
pub fn try_load_kernel_image<P: crate::Platform>(fw_cfg: &mut FwCfg<P>) -> Option<KernelInfo> {
    let file = fw_cfg.get_kernel_file().expect("did not find kernel file");
    let size = file.size();

    let dma_address = PhysAddr::new(DEFAULT_BZIMAGE_START);
    let start_address = crate::phys_to_virt(dma_address);
    log::debug!("Kernel image size {}", size);
    log::debug!("Kernel image start address {:#018x}", start_address.as_u64());
    // Safety: We checked that the DMA address is suitable and big enough.
    let buf = unsafe { slice::from_raw_parts_mut::<u8>(start_address.as_mut_ptr(), size) };

    let actual_size = fw_cfg.read_file(&file, buf).expect("could not read kernel file");
    assert_eq!(actual_size, size, "kernel size did not match expected size");

    let measurement = buf.measure();

    // For a bzImage the 64-bit entry point is at offset 0x200 from the start of the
    // 64-bit kernel. See <https://www.kernel.org/doc/html/v6.3/x86/boot.html>.
    let entry = start_address + 0x200usize;
    log::debug!("Kernel entry point {:#018x}", entry.as_u64());
    Some(KernelInfo { start_address, size, entry, measurement })
}
