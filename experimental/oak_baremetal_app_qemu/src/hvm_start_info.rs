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

include!(concat!(env!("OUT_DIR"), "/start_info.rs"));

impl E820Entry for hvm_memmap_table_entry {
    fn entry_type(&self) -> E820EntryType {
        E820EntryType::from_repr(self.type_).unwrap()
    }

    fn addr(&self) -> usize {
        self.addr.try_into().unwrap()
    }

    fn size(&self) -> usize {
        self.size.try_into().unwrap()
    }
}

impl BootInfo<hvm_memmap_table_entry> for hvm_start_info {
    fn protocol(&self) -> &str {
        "PVH Boot Protocol"
    }

    fn e820_table(&self) -> &[hvm_memmap_table_entry] {
        assert!(self.version >= 1 && self.memmap_paddr != 0);
        // This is safe as it follows the PVH protocol, and we panic above if the pointer is clearly
        // invalid or we're using an incompatible PVH protocol version.
        unsafe {
            core::slice::from_raw_parts(
                self.memmap_paddr as *const hvm_memmap_table_entry,
                self.memmap_entries.try_into().unwrap(),
            )
        }
    }

    fn args(&self) -> &CStr {
        if self.cmdline_paddr == 0 {
            return CStr::from_bytes_with_nul(b"\0").unwrap();
        }
        // Safety: we check for a null pointer above; the PVH documentation doesn't say anything
        // about the pointer being potentially invalid.
        unsafe { CStr::from_ptr(self.cmdline_paddr as *const c_char) }
    }
}
