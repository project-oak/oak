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

use kernel::boot::{BootInfo, E820Entry, E820EntryType};

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

impl BootInfo<multiboot_mmap_entry> for multiboot_info {
    fn protocol(&self) -> &str {
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
}
