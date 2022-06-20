//
// Copyright 2022 The Project Oak Authors
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

use bitflags::bitflags;
use core::ffi::{c_char, CStr};
use oak_baremetal_kernel::boot::{BootInfo, E820Entry, E820EntryType};

/// Magic constant that will be in the `EAX` register when loaded by Multiboot.
pub const BOOT_MAGIC: u64 = 0x2BADB002;

bitflags! {
    /// Flags specify data available in the MultibootInfo data structure.
    /// See <https://www.gnu.org/software/grub/manual/multiboot/multiboot.html#Boot-information-format>
    /// for more details.
    pub struct MultibootInfoFlags: u32 {
        /// is there basic lower/upper memory information?
        const MEMORY = 0x00000001;

        /// is there a boot device set?
        const BOOTDEV = 0x00000002;

        /// is the command-line defined?
        const CMDLINE = 0x00000004;

        /// are there modules to do something with?
        const MODS = 0x00000008;

        /// is there a symbol table loaded?
        /// Mutually exclusive witht ELF_SHDR>.
        const AOUT_SYMS = 0x00000010;

        /// is there an ELF section header table?
        /// Mutually exclusive witht AOUT_SYMS>.
        const ELF_SHDR = 0x00000020;

        /// is there a full memory map?
        const MEM_MAP = 0x00000040;

        /// Is there drive info?
        const DRIVE_INFO = 0x00000080;

        /// Is there a config table?
        const CONFIG_TABLE = 0x00000100;

        /// Is there a boot loader name?
        const BOOT_LOADER_NAME = 0x00000200;

        /// Is there a APM table?
        const APM_TABLE = 0x00000400;

        /// Is there video information?
        const VBE_INFO = 0x00000800;
        const FRAMEBUFFER_INFO = 0x00001000;
    }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct MultibootInfo {
    pub flags: MultibootInfoFlags,
    pub mem_lower: u32,
    pub mem_upper: u32,
    pub boot_device: u32,
    pub cmdline: u32,
    pub mods_count: u32,
    pub mods_addr: u32,
    pub symbols: [u32; 4],
    pub mmap_length: u32,
    pub mmap_addr: u32,
    pub drives_length: u32,
    pub drives_addr: u32,
    pub config_table: u32,
    pub boot_loader_name: u32,
    pub apm_table: u32,
    pub vbe_control_info: u32,
    pub vbe_mode_info: u32,
    pub vbe_mode: u16,
    pub vbe_interface_seg: u16,
    pub vbe_interface_off: u16,
    pub vbe_interface_len: u16,
    pub framebuffer_addr: u64,
    pub framebuffer_pitch: u32,
    pub framebuffer_width: u32,
    pub framebuffer_height: u32,
    pub framebuffer_bpp: u8,
    pub framebuffer_type: u8,
    pub framebuffer_data: [u8; 6],
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct MultibootMmapEntry {
    pub size: u32,
    pub addr: usize,
    pub len: usize,
    pub type_: E820EntryType,
}

impl E820Entry for MultibootMmapEntry {
    fn entry_type(&self) -> E820EntryType {
        self.type_
    }

    fn addr(&self) -> usize {
        self.addr
    }

    fn size(&self) -> usize {
        self.len
    }
}

impl BootInfo<MultibootMmapEntry> for &MultibootInfo {
    fn protocol(&self) -> &'static str {
        "Multiboot1 Protocol"
    }

    fn e820_table(&self) -> &[MultibootMmapEntry] {
        assert!(self.flags.contains(MultibootInfoFlags::MEM_MAP) && self.mmap_length > 0);
        // This is safe as it follows the multiboot protocol, and we panic above if the pointer is
        // clearly invalid or we don't have memory information according to flags.
        // Each entry is 24 bytes (4*u32) and mmap_length is in bytes, thus we have to do the
        // division.
        unsafe {
            core::slice::from_raw_parts(
                self.mmap_addr as *const MultibootMmapEntry,
                self.mmap_length as usize / core::mem::size_of::<MultibootMmapEntry>(),
            )
        }
    }

    fn args(&self) -> &CStr {
        if self.flags.contains(MultibootInfoFlags::CMDLINE) {
            // Safety: the pointer is valid per Multiboot specs if the flag above is set.
            unsafe { CStr::from_ptr(self.cmdline as *const c_char) }
        } else {
            Default::default()
        }
    }
}

/// Magic number identifying the Multiboot header.
#[repr(u32)]
enum Magic {
    MULTIBOOT1 = 0x1BADB002,
}

bitflags! {
    /// Flags specify features requested or required from an boot loader.
    ///
    /// See <https://www.gnu.org/software/grub/manual/multiboot/multiboot.html#Header-magic-fields>
    /// for more details.
    struct HeaderFlags: u32 {
        /// Align all boot modules on i386 page (4KB) boundaries.
        const PAGE_ALIGN = 0x00000001;

        /// Must pass memory information to OS.
        const MEMORY_INFO = 0x00000002;

        /// Must pass video information to OS.
        const VIDEO_MODE = 0x00000004;

        /// This flag indicates the use of the address fields in the header.
        const AOUT_KLUDGE = 0x00010000;
    }
}

/// Multiboot header.
///
/// The Multiboot header must be contained completely within the first 8192 bytes of the OS image,
/// and must be longword (32-bit) aligned. In general, it should come as early as possible, and may
/// be embedded in the beginning of the text segment after the real executable header.
///
/// See <https://www.gnu.org/software/grub/manual/multiboot/multiboot.html#OS-image-format> for
/// more details.
#[repr(C, packed(4))]
pub struct Header {
    magic: Magic,
    flags: HeaderFlags,
    checksum: u32,
}

/// Constructs a Multiboot1 header, with the correct checksum, and the provided flags.
const fn build_multboot_header(flags: HeaderFlags) -> Header {
    Header {
        magic: Magic::MULTIBOOT1,
        flags,
        checksum: (0x100000000u64 - (Magic::MULTIBOOT1 as u64 + flags.bits() as u64)) as u32,
    }
}

#[link_section = ".multiboot_header"]
#[used]
pub static MULTIBOOT_HEADER: Header = build_multboot_header(HeaderFlags::MEMORY_INFO);
