//
// Copyright 2025 The Project Oak Authors
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
use core::{iter::Iterator, mem::MaybeUninit};

use crate::{serial, serial::Debug};
#[unsafe(no_mangle)]
static mut TD_HOB_START: MaybeUninit<HandoffInfoTable> = MaybeUninit::uninit(); // Keep named as in layout.ld

const EFI_HOB_TYPE_HANDOFF: u16 = 0x0001;
const EFI_HOB_TYPE_RESOURCE_DESCRIPTOR: u16 = 0x0003;
const EFI_HOB_TYPE_END_OF_HOB_LIST: u16 = 0xFFFF;

/// UEFI Standard HoB Header.
/// See UEFI Platform Initialization Specification, section 5.2.
/// https://uefi.org/sites/default/files/resources/PI_Spec_1_6.pdf
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Header {
    pub hob_type: u16,
    pub hob_length: u16,
    pub reserved: u32,
}

impl Header {
    pub fn is_resource_descriptor(&self) -> bool {
        self.hob_type == EFI_HOB_TYPE_RESOURCE_DESCRIPTOR && self.hob_length == 0x30
    }

    pub fn is_end_of_hob_list(&self) -> bool {
        self.hob_type == EFI_HOB_TYPE_END_OF_HOB_LIST
    }
}

/// UEFI Standard Handoff Info Table (PHIT HOB).
/// See UEFI Platform Initialization Specification, section 5.3.
/// https://uefi.org/sites/default/files/resources/PI_Spec_1_6.pdf
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct HandoffInfoTable {
    pub header: Header,
    pub version: u32,
    pub boot_mode: u32,
    pub memory_top: u64,
    pub memory_bottom: u64,
    pub free_memory_top: u64,
    pub free_memory_bottom: u64,
    pub end_of_hob_list: u64,
}

/// UEFI Standard Resource Descriptor (HoB)
/// See UEFI Platform Initialization Specification, section 5.5.
/// https://uefi.org/sites/default/files/resources/PI_Spec_1_6.pdf
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct ResourceDescription {
    pub header: Header,
    pub owner: [u8; 16], // Guid
    pub resource_type: u32,
    pub resource_attribute: u32,
    pub physical_start: u64,
    pub resource_length: u64,
}

pub fn get_hit() -> Result<HandoffInfoTable, &'static str> {
    // SAFETY: We assume a valid HOB is input by the VM so the `TD_HOB_START`
    // contains a valid HIT.
    let hit = unsafe { TD_HOB_START.assume_init() };
    serial::debug!("HOB TYPE: ", hit.header.hob_type as u32);
    serial::debug!("HOB LENGTH: ", hit.header.hob_length as u32);
    serial::debug!("HOB VERSION: ", hit.version);
    serial::debug!("HOB BOOT MODE: ", hit.boot_mode);
    serial::debug!("HOB MEMORY TOP: ", hit.memory_top);
    serial::debug!("HOB MEMORY BOTTOM: ", hit.memory_bottom);
    serial::debug!("HOB FREE MEMORY TOP: ", hit.free_memory_top);
    serial::debug!("HOB FREE MEMORY BOTTOM: ", hit.free_memory_bottom);
    serial::debug!("HOB END OF HOB LIST: ", hit.end_of_hob_list);

    if hit.header.hob_length as usize != size_of::<HandoffInfoTable>()
        || hit.header.hob_type != EFI_HOB_TYPE_HANDOFF
    {
        return Err("Corrupted TD HoB header");
    }
    Ok(hit)
}

pub fn get_hob_start() -> *const HandoffInfoTable {
    // SAFETY: We assume a valid HOB is input by the VM so the `TD_HOB_START`
    // contains a valid HIT.
    unsafe { TD_HOB_START.as_ptr() }
}

/// Iterator over HOBs in the HandoffInfoTable
pub struct HobIterator {
    current_hob: *const Header,
    end_of_hob_list: u64,
}

impl Iterator for HobIterator {
    type Item = *const Header;

    fn next(&mut self) -> Option<Self::Item> {
        if (self.current_hob as u64) < self.end_of_hob_list {
            let current = self.current_hob;
            self.current_hob =
                unsafe { self.current_hob.byte_offset((*current).hob_length as isize) };
            Some(current)
        } else {
            serial::debug!("End of HOB list reached", self.current_hob as u64);
            None
        }
    }
}

impl IntoIterator for &HandoffInfoTable {
    type Item = *const Header;
    type IntoIter = HobIterator;

    fn into_iter(self) -> Self::IntoIter {
        // SAFETY: We assume a valid HOB is input by the VM so the `TD_HOB_START`
        // contains a valid HIT.
        let first_hob = unsafe {
            TD_HOB_START.as_ptr().byte_offset(self.header.hob_length as isize) as *const Header
        };
        HobIterator { current_hob: first_hob, end_of_hob_list: self.end_of_hob_list }
    }
}
