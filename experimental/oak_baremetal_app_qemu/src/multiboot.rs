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

// Required as Bindgen-generated code doesn't follow idiomatic Rust style.
#![allow(non_camel_case_types)]

use bitflags::bitflags;
use core::ffi::{c_char, CStr};
use oak_baremetal_kernel::boot::{BootInfo, E820Entry, E820EntryType};

include!(concat!(env!("OUT_DIR"), "/multiboot.rs"));

impl E820Entry for multiboot_mmap_entry {
    fn entry_type(&self) -> E820EntryType {
        E820EntryType::from_repr(self.type_).unwrap()
    }

    fn addr(&self) -> usize {
        self.addr.try_into().unwrap()
    }

    fn size(&self) -> usize {
        self.len.try_into().unwrap()
    }
}

impl BootInfo<multiboot_mmap_entry> for &multiboot_info {
    fn protocol(&self) -> &'static str {
        "Multiboot1 Protocol"
    }

    fn e820_table(&self) -> &[multiboot_mmap_entry] {
        // Bit 6 indicates mmap_* fields are valid.
        assert!(self.flags & (1 << 6) != 0 && self.mmap_length > 0);
        // This is safe as it follows the multiboot protocol, and we panic above if the pointer is
        // clearly invalid or we don't have memory information according to flags.
        // Each entry is 24 bytes (4*u32) and mmap_length is in bytes, thus we have to do the
        // division.
        unsafe {
            core::slice::from_raw_parts(
                self.mmap_addr as *const multiboot_mmap_entry,
                (self.mmap_length / 24).try_into().unwrap(),
            )
        }
    }

    fn args(&self) -> &CStr {
        // Bit 2 indicates cmdline is valid.
        if self.flags & (1 << 2) == 0 {
            Default::default()
        } else {
            // Safety: the pointer is valid per Multiboot specs if the flag above is set.
            unsafe { CStr::from_ptr(self.cmdline as *const c_char) }
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
        const MULTIBOOT_PAGE_ALIGN = 0x00000001;

        /// Must pass memory information to OS.
        const MULTIBOOT_MEMORY_INFO = 0x00000002;

        /// Must pass video information to OS.
        const MULTIBOOT_VIDEO_MODE = 0x00000004;

        /// This flag indicates the use of the address fields in the header.
        const MULTIBOOT_AOUT_KLUDGE = 0x00010000;
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
pub static MULTIBOOT_HEADER: Header = build_multboot_header(HeaderFlags::MULTIBOOT_MEMORY_INFO);
