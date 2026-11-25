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

use core::mem::{MaybeUninit, size_of};

use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

#[unsafe(no_mangle)]
static mut TD_HOB_START: MaybeUninit<HandoffInfoTable> = MaybeUninit::uninit(); // Keep named as in layout.ld

// HOB generic header types.
// See Section 5.2 of the UEFI Platform Initialization Specification v1.8 (Vol.
// 3): <https://uefi.org/specs/PI/1.8/V3_HOB_Code_Definitions.html>
const EFI_HOB_TYPE_HANDOFF: u16 = 0x0001;
const EFI_HOB_TYPE_RESOURCE_DESCRIPTOR: u16 = 0x0003;
const EFI_HOB_TYPE_END_OF_HOB_LIST: u16 = 0xFFFF;

/// Size in bytes of the fixed TD HOB region in `stage0_bin_tdx/layout.ld`.
/// Keep in sync with `layout.ld`.
const TD_HOB_SIZE: u64 = 0x2000;

/// UEFI PI generic HOB header (`EFI_HOB_GENERIC_HEADER`).
///
/// See Section 5.2 of the UEFI Platform Initialization Specification v1.8
/// (Vol. 3): <https://uefi.org/specs/PI/1.8/V3_HOB_Code_Definitions.html>
#[repr(C)]
#[derive(Copy, Clone, Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
pub struct Header {
    pub hob_type: u16,
    pub hob_length: u16,
    pub reserved: u32,
}

/// UEFI PI Handoff Info Table (`EFI_HOB_HANDOFF_INFO_TABLE`, PHIT HOB).
///
/// See Section 5.3 of the UEFI Platform Initialization Specification v1.8
/// (Vol. 3): <https://uefi.org/specs/PI/1.8/V3_HOB_Code_Definitions.html>
#[repr(C)]
#[derive(Copy, Clone, Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
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

/// UEFI PI Resource Descriptor HOB (`EFI_HOB_RESOURCE_DESCRIPTOR`).
///
/// See Section 5.5 of the UEFI Platform Initialization Specification v1.8
/// (Vol. 3): <https://uefi.org/specs/PI/1.8/V3_HOB_Code_Definitions.html>
#[repr(C)]
#[derive(Copy, Clone, Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
pub struct ResourceDescription {
    pub header: Header,
    pub owner: [u8; 16],
    pub resource_type: u32,
    pub resource_attribute: u32,
    pub physical_start: u64,
    pub resource_length: u64,
}

pub fn get_hob_start() -> *const HandoffInfoTable {
    // SAFETY: Returns the static address of `.tdx.td_hob` without dereferencing.
    unsafe { TD_HOB_START.as_ptr() }
}

/// Returns the fixed `TD_HOB_SIZE` byte slice reserved for `.tdx.td_hob` in
/// `layout.ld`.
pub fn get_hob_region() -> &'static [u8] {
    // SAFETY: `TD_HOB_START` is the base of the `TD_HOB_SIZE` `.tdx.td_hob`
    // section declared in `layout.ld` and is read-only after TD creation.
    unsafe { core::slice::from_raw_parts(get_hob_start() as *const u8, TD_HOB_SIZE as usize) }
}

/// Parses a TD HOB list starting with [`HandoffInfoTable`] into `dest`,
/// returning the number of [`BootE820Entry`] records written.
#[allow(clippy::if_same_then_else)]
pub fn parse_hob_e820_entries(
    hob_region: &[u8],
    hob_base: u64,
    mailbox_base: u64,
    dest: &mut [BootE820Entry],
) -> Result<usize, &'static str> {
    let (hit, _) =
        HandoffInfoTable::read_from_prefix(hob_region).map_err(|_| "corrupted TD HOB header")?;
    if hit.header.hob_length as usize != size_of::<HandoffInfoTable>()
        || hit.header.hob_type != EFI_HOB_TYPE_HANDOFF
    {
        return Err("corrupted TD HOB header");
    }

    // Clamp `end_of_hob_list` to the provided `hob_region` slice.
    let bound_len =
        hit.end_of_hob_list.saturating_sub(hob_base).min(hob_region.len() as u64) as usize;
    let mut hob_body = hob_region.get(size_of::<HandoffInfoTable>()..bound_len).unwrap_or(&[]);

    let mut count = 0usize;
    while let Ok((hdr, _)) = Header::read_from_prefix(hob_body) {
        let hob_len = hdr.hob_length as usize;
        if hob_len < size_of::<Header>() || hob_len > hob_body.len() {
            break;
        }
        let (hob_bytes, rest) = hob_body.split_at(hob_len);
        hob_body = rest;

        if hdr.hob_type == EFI_HOB_TYPE_RESOURCE_DESCRIPTOR
            && hob_len == size_of::<ResourceDescription>()
        {
            let (desc, _) = ResourceDescription::read_from_prefix(hob_bytes)
                .map_err(|_| "corrupted resource descriptor in TD HOB")?;

            let slot = dest.get_mut(count).ok_or("too many resource descriptors in TD HOB")?;

            let entry_type = if desc.physical_start == hob_base {
                E820EntryType::NVS
            } else if desc.physical_start == mailbox_base {
                E820EntryType::NVS
            } else if desc.physical_start == 0 {
                E820EntryType::RAM
            } else if desc.resource_type == 0 {
                E820EntryType::RESERVED
            } else {
                E820EntryType::RAM
            };

            *slot = BootE820Entry::new(
                desc.physical_start as usize,
                desc.resource_length as usize,
                entry_type,
            );
            count += 1;
        } else if hdr.hob_type == EFI_HOB_TYPE_END_OF_HOB_LIST {
            break;
        } else {
            return Err("unknown HOB type in TD HOB");
        }
    }

    if count == 0 { Err("no valid TD HOB found") } else { Ok(count) }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use googletest::prelude::*;

    use super::*;

    const TEST_HOB_BASE: u64 = 0x10_0000;
    const TEST_MAILBOX_BASE: u64 = 0x10_2000;

    fn push_header(buf: &mut Vec<u8>, hob_type: u16, hob_length: u16) {
        buf.extend_from_slice(&hob_type.to_le_bytes());
        buf.extend_from_slice(&hob_length.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
    }

    fn new_hob_region(end_of_hob_list: u64) -> Vec<u8> {
        let mut buf = Vec::new();
        push_header(&mut buf, EFI_HOB_TYPE_HANDOFF, size_of::<HandoffInfoTable>() as u16);
        buf.extend_from_slice(&9u32.to_le_bytes()); // version
        buf.extend_from_slice(&0u32.to_le_bytes()); // boot_mode
        buf.extend_from_slice(&0u64.to_le_bytes()); // memory_top
        buf.extend_from_slice(&0u64.to_le_bytes()); // memory_bottom
        buf.extend_from_slice(&0u64.to_le_bytes()); // free_memory_top
        buf.extend_from_slice(&0u64.to_le_bytes()); // free_memory_bottom
        buf.extend_from_slice(&end_of_hob_list.to_le_bytes());
        buf
    }

    fn set_end_of_hob_list(buf: &mut [u8], end_of_hob_list: u64) {
        let offset = size_of::<HandoffInfoTable>() - size_of::<u64>();
        buf[offset..size_of::<HandoffInfoTable>()].copy_from_slice(&end_of_hob_list.to_le_bytes());
    }

    fn push_resource(
        buf: &mut Vec<u8>,
        resource_type: u32,
        physical_start: u64,
        resource_length: u64,
    ) {
        push_header(buf, EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, size_of::<ResourceDescription>() as u16);
        buf.extend_from_slice(&[0u8; 16]); // owner
        buf.extend_from_slice(&resource_type.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // resource_attribute
        buf.extend_from_slice(&physical_start.to_le_bytes());
        buf.extend_from_slice(&resource_length.to_le_bytes());
    }

    fn push_raw_hob(buf: &mut Vec<u8>, hob_type: u16, payload_len: usize) {
        let total = size_of::<Header>() + payload_len;
        push_header(buf, hob_type, total as u16);
        buf.resize(buf.len() + payload_len, 0);
    }

    fn push_end(buf: &mut Vec<u8>) {
        push_raw_hob(buf, EFI_HOB_TYPE_END_OF_HOB_LIST, 0);
    }

    fn finish_with_end_of_hob_list(buf: &mut [u8]) {
        set_end_of_hob_list(buf, TEST_HOB_BASE + buf.len() as u64);
    }

    #[gtest]
    fn parses_valid_hob_list() {
        let mut buf = new_hob_region(0);
        push_resource(&mut buf, 0, 0x0, 0xA_0000);
        push_resource(&mut buf, 0, 0xF_0000, 0x1_0000);
        push_resource(&mut buf, 0, TEST_HOB_BASE, TD_HOB_SIZE);
        push_resource(&mut buf, 0, TEST_MAILBOX_BASE, 0x1000);
        push_resource(&mut buf, 7, 0x10_3000, 0x7FEF_D000);
        push_end(&mut buf);
        finish_with_end_of_hob_list(&mut buf);
        buf.resize(TD_HOB_SIZE as usize, 0);

        let mut out = [BootE820Entry::default(); 8];
        let count = parse_hob_e820_entries(&buf, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out)
            .expect("valid HOB list");

        expect_that!(
            &out[..count],
            eq(&[
                BootE820Entry::new(0x0, 0xA_0000, E820EntryType::RAM),
                BootE820Entry::new(0xF_0000, 0x1_0000, E820EntryType::RESERVED),
                BootE820Entry::new(
                    TEST_HOB_BASE as usize,
                    TD_HOB_SIZE as usize,
                    E820EntryType::NVS,
                ),
                BootE820Entry::new(TEST_MAILBOX_BASE as usize, 0x1000, E820EntryType::NVS),
                BootE820Entry::new(0x10_3000, 0x7FEF_D000, E820EntryType::RAM),
            ][..])
        );
    }

    #[gtest]
    fn stops_before_truncated_body_partial_header_or_zero_length_entry() {
        let mut out = [BootE820Entry::default(); 4];

        // A resource descriptor whose 0x30-byte body runs past the bound stops
        // iteration.
        let mut truncated_body = new_hob_region(0);
        push_resource(&mut truncated_body, 7, 0x10_3000, 0x10_0000);
        push_header(
            &mut truncated_body,
            EFI_HOB_TYPE_RESOURCE_DESCRIPTOR,
            size_of::<ResourceDescription>() as u16,
        );
        truncated_body.resize(truncated_body.len() + 16, 0);
        finish_with_end_of_hob_list(&mut truncated_body);
        expect_that!(
            parse_hob_e820_entries(&truncated_body, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            ok(eq(1))
        );

        // Only 4 trailing bytes remain (partial header).
        let mut partial_header = new_hob_region(0);
        push_resource(&mut partial_header, 7, 0x10_3000, 0x10_0000);
        partial_header.resize(partial_header.len() + 4, 0);
        finish_with_end_of_hob_list(&mut partial_header);
        expect_that!(
            parse_hob_e820_entries(&partial_header, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            ok(eq(1))
        );

        // Zero-length entry stops iteration instead of looping forever.
        let mut zero_len = new_hob_region(0);
        push_resource(&mut zero_len, 7, 0x10_3000, 0x10_0000);
        push_header(&mut zero_len, EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, 0);
        finish_with_end_of_hob_list(&mut zero_len);
        expect_that!(
            parse_hob_e820_entries(&zero_len, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            ok(eq(1))
        );
    }

    #[gtest]
    fn rejects_corrupted_unknown_empty_or_overflowing_hob_lists() {
        let mut out = [BootE820Entry::default(); 8];

        // Corrupted PHIT header (wrong type/length or short buffer).
        expect_that!(
            parse_hob_e820_entries(&[0u8; 64], TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            err(eq("corrupted TD HOB header"))
        );
        expect_that!(
            parse_hob_e820_entries(&[0u8; 8], TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            err(eq("corrupted TD HOB header"))
        );

        // Wrong resource descriptor length is rejected.
        let mut bad_desc_len = new_hob_region(0);
        push_raw_hob(&mut bad_desc_len, EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, 16);
        push_end(&mut bad_desc_len);
        finish_with_end_of_hob_list(&mut bad_desc_len);
        expect_that!(
            parse_hob_e820_entries(&bad_desc_len, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            err(eq("unknown HOB type in TD HOB"))
        );

        // Unknown HOB type.
        let mut unknown_hob = new_hob_region(0);
        push_raw_hob(&mut unknown_hob, 0x1234, 0);
        push_end(&mut unknown_hob);
        finish_with_end_of_hob_list(&mut unknown_hob);
        expect_that!(
            parse_hob_e820_entries(&unknown_hob, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            err(eq("unknown HOB type in TD HOB"))
        );

        // Empty descriptor list (no resource descriptors before END_OF_HOB_LIST).
        let mut empty_list = new_hob_region(0);
        push_end(&mut empty_list);
        finish_with_end_of_hob_list(&mut empty_list);
        expect_that!(
            parse_hob_e820_entries(&empty_list, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut out),
            err(eq("no valid TD HOB found"))
        );

        // Destination slice too small.
        let mut small_out = [BootE820Entry::default(); 1];
        let mut two_entries = new_hob_region(0);
        push_resource(&mut two_entries, 0, 0x0, 0xA_0000);
        push_resource(&mut two_entries, 7, 0x10_3000, 0x10_0000);
        push_end(&mut two_entries);
        finish_with_end_of_hob_list(&mut two_entries);
        expect_that!(
            parse_hob_e820_entries(&two_entries, TEST_HOB_BASE, TEST_MAILBOX_BASE, &mut small_out),
            err(eq("too many resource descriptors in TD HOB"))
        );
    }
}
