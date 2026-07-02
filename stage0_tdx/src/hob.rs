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

/// Size in bytes of the memory region reserved for the TD HOB list.
///
/// The VMM writes the HOB list into this fixed-size region, so the walk over it
/// must never leave these bounds. Keep in sync with `TD_HOB_SIZE` in layout.ld.
const TD_HOB_SIZE: u64 = 0x2000;

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
        let current = self.current_hob;
        let start = current as u64;
        // `end_of_hob_list` and every `hob_length` come from the untrusted
        // VMM, so only walk an entry that lies entirely below the bound: the
        // header dereferenced here, and the full HOB body the callers read (a
        // 0x30-byte ResourceDescription in `prefill_e820_table`), must fit.
        if start.checked_add(size_of::<Header>() as u64)? > self.end_of_hob_list {
            serial::debug!("End of HOB list reached", start);
            return None;
        }
        // SAFETY: the header lies fully within the region bounded above.
        let hob_length = unsafe { (*current).hob_length } as u64;
        // A HOB is at least a header long; a shorter (or zero) length would
        // never advance the cursor and could loop forever.
        if hob_length < size_of::<Header>() as u64
            || start.checked_add(hob_length)? > self.end_of_hob_list
        {
            serial::debug!("End of HOB list reached", start);
            return None;
        }
        self.current_hob = unsafe { current.byte_offset(hob_length as isize) };
        Some(current)
    }
}

impl IntoIterator for &HandoffInfoTable {
    type Item = *const Header;
    type IntoIter = HobIterator;

    fn into_iter(self) -> Self::IntoIter {
        // SAFETY: We assume a valid HOB is input by the VM so the `TD_HOB_START`
        // contains a valid HIT.
        let hob_start = get_hob_start() as u64;
        // The host-supplied `end_of_hob_list` is otherwise unbounded; clamp it
        // to the reserved HOB region so the walk can never leave it.
        let end_of_hob_list = self.end_of_hob_list.min(hob_start.saturating_add(TD_HOB_SIZE));
        // SAFETY: We assume a valid HOB is input by the VM so the `TD_HOB_START`
        // contains a valid HIT.
        let first_hob = unsafe {
            TD_HOB_START.as_ptr().byte_offset(self.header.hob_length as isize) as *const Header
        };
        HobIterator { current_hob: first_hob, end_of_hob_list }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Writes a HOB header at `offset` in `buf`. Callers keep it in bounds.
    fn write_header(buf: &mut [u8], offset: usize, hob_type: u16, hob_length: u16) {
        let header = Header { hob_type, hob_length, reserved: 0 };
        // SAFETY: `offset + size_of::<Header>() <= buf.len()` for every caller.
        unsafe { core::ptr::write(buf.as_mut_ptr().add(offset) as *mut Header, header) };
    }

    // Builds an iterator over `buf` with `end_of_hob_list` at the slice end,
    // mirroring the bound `into_iter` applies to the real HOB region.
    fn iter_over(buf: &[u8]) -> HobIterator {
        HobIterator {
            current_hob: buf.as_ptr() as *const Header,
            end_of_hob_list: buf.as_ptr() as u64 + buf.len() as u64,
        }
    }

    #[test]
    fn yields_entry_fully_within_bound() {
        let mut buf = [0u8; 0x38];
        write_header(&mut buf, 0, EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, 0x30);
        assert!(iter_over(&buf).next().is_some());
    }

    #[test]
    fn stops_before_entry_body_crosses_bound() {
        // A resource descriptor whose 0x30-byte body runs past the bound: the
        // header fits but the body the caller reads would not.
        let mut buf = [0u8; 0x20];
        write_header(&mut buf, 0, EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, 0x30);
        assert!(iter_over(&buf).next().is_none());
    }

    #[test]
    fn stops_before_partial_header() {
        // Only 4 bytes remain, not enough for the 8-byte header to dereference.
        let buf = [0u8; 4];
        assert!(iter_over(&buf).next().is_none());
    }

    #[test]
    fn stops_on_zero_length_entry() {
        // A zero-length entry would never advance the cursor.
        let mut buf = [0u8; 0x10];
        write_header(&mut buf, 0, EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, 0);
        assert!(iter_over(&buf).next().is_none());
    }
}
