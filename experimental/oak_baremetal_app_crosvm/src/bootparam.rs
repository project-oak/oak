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

impl E820Entry for BootE820Entry {
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

impl BootInfo<BootE820Entry> for &BootParams {
    fn protocol(&self) -> &'static str {
        "Linux Boot Protocol"
    }

    fn e820_table(&self) -> &[BootE820Entry] {
        &self.e820_table[..self.e820_entries as usize]
    }

    fn args(&self) -> &CStr {
        if self.hdr.cmdline_size == 0 {
            Default::default()
        } else {
            // Safety: Linux boot protocol expects the pointer to be valid, even if there are no
            // args.
            unsafe { CStr::from_ptr(self.hdr.cmd_line_ptr as *const c_char) }
        }
    }
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
struct SetupHeader {
    padding1: [u8; 55usize],
    cmd_line_ptr: u32,
    padding2: [u8; 12usize],
    cmdline_size: u32,
    padding3: [u8; 48usize],
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct BootE820Entry {
    addr: usize,
    size: usize,
    type_: E820EntryType,
}

#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct BootParams {
    _padding1: [u8; 488usize],
    e820_entries: u8,
    _padding2: [u8; 8usize],
    hdr: SetupHeader,
    _padding3: [u8; 100usize],
    e820_table: [BootE820Entry; 128usize],
    _padding4: [u8; 816usize],
}
static_assertions::assert_eq_size!(BootParams, [u8; 4096usize]);
