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

use core::ffi::{c_char, CStr};
use oak_baremetal_kernel::boot::{BootInfo, E820Entry, E820EntryType};

/// Magic value that needs to be present in the <StartInfo::magic> field.
/// ("xEn3" with the 0x80 bit of the "E" set).
#[cfg(not(feature = "multiboot"))]
pub const BOOT_MAGIC: u32 = 0x336ec578;

// StartInfo and MemmapTableEntry are based on data structures generated with bindgen from Xen
// public/arch-x86/hvm/start_info.h.
#[repr(C)]
pub struct StartInfo {
    /// Contains the magic value 0x336ec578 "xEn3" with the 0x80 bit of the "E" set).
    pub magic: u32,

    /// Version of this structure.
    pub version: u32,

    /// SIF_xxx flags.
    pub flags: u32,

    /// Number of modules passed to the kernel.
    pub nr_modules: u32,

    /// Physical address of an array of vm_modlist_entry.
    pub modlist_paddr: u64,

    /// Physical address of the command line.
    pub cmdline_paddr: *const c_char,

    /// hysical address of the RSDP ACPI data structure.
    pub rsdp_paddr: u64,

    /// Physical address of an array of hvm_memmap_table_entry.
    /// Present only for version 1 and newer.
    pub memmap_paddr: *const MemmapTableEntry,

    /// Number of entries in the memmap table.
    /// Present only for version 1 and newer.
    /// Value will be zero if there is no memory map being provided.
    pub memmap_entries: u32,

    /// Must be zero.
    /// Present only for version 1 and newer.
    pub reserved: u32,
}

#[repr(C)]
pub struct MemmapTableEntry {
    /// Base address of the memory region
    pub addr: usize,

    /// Size of the memory region in bytes
    pub size: usize,

    /// Mapping type
    pub type_: E820EntryType,

    /// Must be zero for Version 1.
    pub reserved: u32,
}

impl E820Entry for MemmapTableEntry {
    fn entry_type(&self) -> E820EntryType {
        self.type_
    }

    fn addr(&self) -> usize {
        self.addr
    }

    fn size(&self) -> usize {
        self.size
    }
}

impl BootInfo<MemmapTableEntry> for &StartInfo {
    fn protocol(&self) -> &'static str {
        "PVH Boot Protocol"
    }

    fn e820_table(&self) -> &[MemmapTableEntry] {
        assert!(self.version >= 1 && !self.memmap_paddr.is_null());
        // This is safe as it follows the PVH protocol, and we panic above if the pointer is clearly
        // invalid or we're using an incompatible PVH protocol version.
        unsafe { core::slice::from_raw_parts(self.memmap_paddr, self.memmap_entries as usize) }
    }

    fn args(&self) -> &CStr {
        if self.cmdline_paddr.is_null() {
            Default::default()
        } else {
            // Safety: we check for a null pointer above; the PVH documentation doesn't say
            // anything about the pointer being potentially invalid.
            unsafe { CStr::from_ptr(self.cmdline_paddr) }
        }
    }
}
