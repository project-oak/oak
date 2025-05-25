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

use std::{collections::HashMap, mem::size_of};

use log::trace;
use x86_64::PhysAddr;
use zerocopy::AsBytes;

/// The header of a guid table entry.
///
/// The table footer also has the same structure.
struct GuidTableEntryHeader {
    guid: u128,
    size: u16,
}

impl GuidTableEntryHeader {
    fn parse(bytes: &[u8]) -> Self {
        assert!(bytes.len() >= GUID_TABLE_ENTRY_HEADER_SIZE);
        let mut guid: u128 = 0;
        let guid_end = bytes.len();
        let guid_start = guid_end - size_of::<u128>();
        guid.as_bytes_mut().copy_from_slice(&bytes[guid_start..guid_end]);
        let mut size: u16 = 0;
        let size_start = guid_start - size_of::<u16>();
        size.as_bytes_mut().copy_from_slice(&bytes[size_start..guid_start]);
        Self { guid, size }
    }
}

/// The address of the first byte after the end of the firmware image.
///
/// The firmware image gets loaded just below the 4GiB boundary.
const FIRMWARE_TOP: PhysAddr = PhysAddr::new(0x1_0000_0000);

/// The address of the first byte after the end of the legacy boot shadow
/// firmware image.
///
/// To support legacy booting the last 128KiB of the firmware gets shadowed just
/// below the end of 20-bit memory.
const LEGACY_TOP: PhysAddr = PhysAddr::new(0x10_0000);

/// The maximum size of the shadow firmware for legacy boot.
const LEGACY_MAX_SIZE: usize = 128 * 1024;

/// The reverse offset from the end of the firmware blob to the end of the GUID
/// tables.
const GUID_TABLE_END_OFFSET: usize = 0x20;

/// The size of the header of an entry in the GUID table.
///
/// The header consists of a 16 byte GUID and a 16-bit length field.
const GUID_TABLE_ENTRY_HEADER_SIZE: usize = size_of::<u128>() + size_of::<u16>();

/// The footer GUID identifying the end of the GUID table.
///
/// This matches the footer GUID used in OVMF
/// (96b582de-1fb2-45f7-baea-a366c55a082d).
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm>.
const GUID_TABLE_FOOTER_GUID: u128 = u128::from_le_bytes([
    0xDE, 0x82, 0xB5, 0x96, 0xB2, 0x1F, 0xF7, 0x45, 0xBA, 0xEA, 0xA3, 0x66, 0xC5, 0x5A, 0x08, 0x2D,
]);

/// The contents of the Stage 0 firmware ROM image and its associated metadata.
pub struct Stage0Info {
    /// The bytes of the State 0 firmware ROM image.
    pub bytes: Vec<u8>,
    /// The start address of the firmware ROM in guest memory.
    pub start_address: PhysAddr,
    /// The start address of the legacy boot shadow of the firmware ROM in guest
    /// memory.
    pub legacy_start_address: PhysAddr,
    /// The offset into the firmware ROM image from where the legacy boot shadow
    /// starts.
    legacy_offset: usize,
}

impl Stage0Info {
    /// Gets the bytes of the entire ROM image.
    pub fn rom_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Gets the bytes of the legacy boot shadow of the ROM image.
    pub fn legacy_shadow_bytes(&self) -> &[u8] {
        &self.bytes[self.legacy_offset..]
    }

    /// Parses the GUID table from the firmware image as a map.
    ///
    /// The GUID (represented as a u128) of each table entry is the key and the
    /// associated data of the entry is the value.
    pub fn parse_firmware_guid_table(&self) -> HashMap<u128, &[u8]> {
        let content = self.get_guid_table_content();
        let mut entry_end = content.len();
        let mut result = HashMap::new();
        while entry_end > GUID_TABLE_ENTRY_HEADER_SIZE {
            let GuidTableEntryHeader { guid: entry_guid, size: entry_size } =
                GuidTableEntryHeader::parse(&content[..entry_end]);
            assert!(entry_end >= entry_size as usize, "invalid entry size");
            let content_end = entry_end - GUID_TABLE_ENTRY_HEADER_SIZE;
            let content_start = entry_end - entry_size as usize;
            if let Some(_existing) = result.insert(entry_guid, &content[content_start..content_end])
            {
                panic!("duplicate GUID detected in table");
            }
            entry_end = content_start;
        }
        assert_eq!(entry_end, 0, "malformed GUID table contents");
        result
    }

    /// Gets the main contents of the GUID table, excluding the footer.
    pub fn get_guid_table_content(&self) -> &[u8] {
        assert!(
            self.bytes.len() > GUID_TABLE_END_OFFSET + GUID_TABLE_ENTRY_HEADER_SIZE,
            "firmware ROM too small"
        );
        // We parse the GUID table from the end, starting at the footer.
        let table_end = self.bytes.len() - GUID_TABLE_END_OFFSET;
        trace!("GUID table end: {}", table_end);
        let GuidTableEntryHeader { guid: footer_guid, size: table_size } =
            GuidTableEntryHeader::parse(&self.bytes[..table_end]);
        assert_eq!(
            footer_guid, GUID_TABLE_FOOTER_GUID,
            "firmware image doesn't contain a valid GUID table"
        );
        trace!("GUID table size: {}", table_size);
        assert!(
            table_size as usize > GUID_TABLE_ENTRY_HEADER_SIZE && (table_size as usize) < table_end,
            "invalid GUID table size"
        );
        let content_start = table_end - (table_size as usize);
        let content_end = table_end - GUID_TABLE_ENTRY_HEADER_SIZE;
        &self.bytes[content_start..content_end]
    }

    pub fn new(bytes: Vec<u8>) -> Self {
        let size = bytes.len();
        let start_address = FIRMWARE_TOP - (size as u64);
        let legacy_size = size.min(LEGACY_MAX_SIZE);
        let legacy_start_address = LEGACY_TOP - (legacy_size as u64);
        let legacy_offset = size - legacy_size;
        Self { bytes, start_address, legacy_start_address, legacy_offset }
    }
}
