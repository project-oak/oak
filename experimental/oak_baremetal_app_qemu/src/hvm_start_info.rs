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

#[repr(C)]
pub struct StartInfo {
    pub magic: u32,
    pub version: u32,
    pub flags: u32,
    pub nr_modules: u32,
    pub modlist_paddr: u64,
    pub cmdline_paddr: *const c_char,
    pub rsdp_paddr: u64,
    pub memmap_paddr: *const MemmapTableEntry,
    pub memmap_entries: u32,
    pub reserved: u32,
}
#[repr(C)]
pub struct MemmapTableEntry {
    pub addr: usize,
    pub size: usize,
    pub type_: E820EntryType,
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
