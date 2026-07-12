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

use alloc::{boxed::Box, ffi::CString, string::String, vec};
use core::{ffi::c_void, slice};

use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use x86_64::{PhysAddr, VirtAddr};

use crate::{Measured, fw_cfg::FwCfg};

unsafe extern "C" {
    #[link_name = "stack_start"]
    static BOOT_STACK_POINTER: c_void;
}

/// The default location for loading a compressed (bzImage format) kerne.
const DEFAULT_BZIMAGE_START: u64 = 0x2000000; // See b/359144829 before changing.

/// Returns whether a kernel image of `size` bytes loaded at the fixed
/// [`DEFAULT_BZIMAGE_START`] address is fully contained in a single region of
/// guest RAM that stage0 has identity mapped.
///
/// The image size comes from the untrusted VMM (the fw_cfg `KernelSize` item),
/// so it can be any `u32`. Without this bound a large value makes
/// [`Kernel::try_load_kernel_image`] write past the load region, over unmapped
/// memory or memory that does not back the kernel. The initrd path already
/// bounds its host-supplied size via `find_suitable_dma_address`; this mirrors
/// that for the fixed kernel address.
fn kernel_fits_in_memory(size: usize, e820_table: &[BootE820Entry]) -> bool {
    let start = DEFAULT_BZIMAGE_START;
    let Some(end) = start.checked_add(size as u64) else {
        return false;
    };
    // The kernel is written through the identity map, which only covers the first
    // `TOP_OF_VIRTUAL_MEMORY` bytes.
    if end > crate::TOP_OF_VIRTUAL_MEMORY {
        return false;
    }
    e820_table.iter().any(|entry| {
        entry.entry_type() == Some(E820EntryType::RAM)
            && (entry.addr() as u64) <= start
            && entry
                .addr()
                .checked_add(entry.size())
                .is_some_and(|entry_end| (entry_end as u64) >= end)
    })
}

/// A bzImage-compatible kernel loaded into memory.
#[repr(transparent)]
pub struct Kernel(&'static [u8]);

impl Kernel {
    /// Tries to load a kernel image from the QEMU fw_cfg device.
    ///
    /// We assume that a kernel file provided via the traditional selector is a
    /// compressed kernel using the bzImage format. We assume that a kernel file
    /// provided via the custom filename of "opt/stage0/elf_kernel" is an
    /// uncompressed ELF file.
    ///
    /// If it finds a kernel it returns the information about the kernel,
    /// otherwise `None`.
    ///
    /// # Safety
    ///
    /// We load the kernel directly into memory, bypassing the usual allocation
    /// mechanisms. The caller must guarantee that only one instance of `Kernel`
    /// is alive at any given time.
    pub unsafe fn try_load_kernel_image<P: crate::Platform>(
        fw_cfg: &mut FwCfg<P>,
        e820_table: &[BootE820Entry],
    ) -> Option<Self> {
        let file = fw_cfg.get_kernel_file().expect("did not find kernel file");
        let size = file.size();

        // The size is supplied by the untrusted VMM. Reject a kernel that would not
        // fit at the fixed load address before forming the destination slice, so we
        // never write past the mapped RAM that backs it.
        assert!(
            kernel_fits_in_memory(size, e820_table),
            "kernel image of {size} bytes does not fit in mapped guest memory"
        );

        let dma_address = PhysAddr::new(DEFAULT_BZIMAGE_START);
        let start_address = crate::phys_to_virt(dma_address);
        log::debug!("Kernel image size {}", size);
        log::debug!("Kernel image start address {:#018x}", start_address.as_u64());
        // Safety: we checked above that `size` bytes at `DEFAULT_BZIMAGE_START` lie
        // within mapped RAM.
        let buf = unsafe { slice::from_raw_parts_mut::<u8>(start_address.as_mut_ptr(), size) };
        let actual_size = fw_cfg.read_file(&file, buf).expect("could not read kernel file");
        assert_eq!(actual_size, size, "kernel size did not match expected size");

        let kernel = Self(buf);
        log::debug!("Kernel entry point {:#018x}", kernel.entry());
        Some(kernel)
    }

    pub fn start(&self) -> VirtAddr {
        VirtAddr::from_ptr(self.0.as_ptr())
    }

    pub fn entry(&self) -> VirtAddr {
        // Safety: For a bzImage the 64-bit entry point is at offset 0x200 from the
        // start of the 64-bit kernel. See <https://www.kernel.org/doc/html/v6.3/x86/boot.html>.
        VirtAddr::from_ptr(unsafe { self.0.as_ptr().add(0x200) })
    }

    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Passes control to the operating system kernel. No more code from the
    /// BIOS will run.
    ///
    /// # Safety
    ///
    /// This assumes that the kernel entry point is valid.
    pub unsafe fn jump_to_kernel<A: core::alloc::Allocator>(
        self,
        zero_page: Box<crate::zero_page::ZeroPage, &A>,
    ) -> ! {
        unsafe {
            core::arch::asm!(
                // Boot stack pointer
                "mov {1}, %rsp",
                // Zero page address
                "mov {2}, %rsi",
                // ...and away we go!
                "jmp *{0}",
                in(reg) self.entry().as_u64(),
                in(reg) &BOOT_STACK_POINTER as *const _ as u64,
                in(reg) Box::leak(zero_page),
                options(noreturn, att_syntax)
            );
        }
    }
}

impl Measured for Kernel {
    fn measure(&self) -> crate::Measurement {
        self.0.measure()
    }
}

#[derive(Default)]
pub struct KernelCmdLine {
    kernel_cmdline: String,
}

impl KernelCmdLine {
    pub fn kernel_cmdline(&self) -> String {
        self.kernel_cmdline.clone()
    }
}

impl Measured for KernelCmdLine {
    fn measure(&self) -> crate::Measurement {
        self.kernel_cmdline.as_bytes().measure()
    }
}

impl Kernel {
    #[allow(dead_code)]
    pub fn as_bytes(&self) -> &[u8] {
        self.0
    }
}

/// Tries to load the kernel command-line from the fw_cfg device.
///
/// We first try to read it using the traditional selector. If it is not
/// available there we try to read it using a custom file path.
pub fn try_load_cmdline<P: crate::Platform>(fw_cfg: &mut FwCfg<P>) -> Option<KernelCmdLine> {
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
    Some(KernelCmdLine { kernel_cmdline: cmdline.clone() })
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;

    fn ram(addr: usize, size: usize) -> BootE820Entry {
        BootE820Entry::new(addr, size, E820EntryType::RAM)
    }

    #[gtest]
    fn accepts_kernel_that_fits_in_ram() {
        // 512 MiB of RAM starting just above the first 1 MiB.
        let e820 = [ram(0x10_0000, 0x2000_0000)];
        // A 64 MiB kernel at 32 MiB ends at 96 MiB, inside RAM and the identity map.
        expect_that!(kernel_fits_in_memory(0x0400_0000, &e820), eq(true));
    }

    #[gtest]
    fn rejects_kernel_past_mapped_window() {
        // RAM extends past the 1 GiB identity map.
        let e820 = [ram(0x10_0000, 0x1_0000_0000)];
        // A ~3.75 GiB size would write far past TOP_OF_VIRTUAL_MEMORY.
        expect_that!(kernel_fits_in_memory(0xF000_0000, &e820), eq(false));
    }

    #[gtest]
    fn rejects_kernel_past_backing_ram() {
        // Only ~513 MiB of RAM is present.
        let e820 = [ram(0x10_0000, 0x2000_0000)];
        // A 544 MiB kernel at 32 MiB ends at 576 MiB: inside the map, past RAM.
        expect_that!(kernel_fits_in_memory(0x2200_0000, &e820), eq(false));
    }

    #[gtest]
    fn rejects_when_no_ram_covers_load_address() {
        // RAM present but entirely below the load address.
        let e820 = [ram(0x0, 0x100_0000)];
        expect_that!(kernel_fits_in_memory(0x1000, &e820), eq(false));
    }
}
