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

use std::{collections::HashMap, mem::size_of, path::PathBuf};

use anyhow::Context;
use log::{debug, info, trace};
use sha2::{Digest, Sha256};
use strum::FromRepr;
use x86_64::{
    structures::paging::{PageSize, Size4KiB},
    PhysAddr,
};
use zerocopy::AsBytes;

use crate::page::PageType;

/// The address of the first byte after the end of the firmware image.
///
/// The firmware image gets loaded just below the 4GiB boundary.
const FIRMWARE_TOP: PhysAddr = PhysAddr::new(0x1_0000_0000);

/// The address of the first byte after the end of the legacy boot shadow firmware image.
///
/// To support legacy booting the last 128KiB of the firmware gets shadowed just below the end of
/// 20-bit memory.
const LEGACY_TOP: PhysAddr = PhysAddr::new(0x10_0000);

/// The maximum size of the shadow firmware for legacy boot.
const LEGACY_MAX_SIZE: usize = 128 * 1024;

/// The reverse offset from the end of the firmware blob to the end of the GUID tables.
const GUID_TABLE_END_OFFSET: usize = 0x20;

/// The size of the header of an entry in the GUID table.
///
/// The header consists of a 16 byte GUID and a 16-bit length field.
const GUID_TABLE_ENTRY_HEADER_SIZE: usize = size_of::<u128>() + size_of::<u16>();

/// The size of the SEV metadata section header.
const SEV_METADATA_HEADER_SIZE: usize = 16;

/// The size of the SEV metadata section entry.
const SEV_METADATA_ENTRY_SIZE: usize = 12;

/// The footer GUID identifying the end of the GUID table.
///
/// This matches the footer GUID used in OVMF (96b582de-1fb2-45f7-baea-a366c55a082d).
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm>.
const GUID_TABLE_FOOTER_GUID: u128 = u128::from_le_bytes([
    0xDE, 0x82, 0xB5, 0x96, 0xB2, 0x1F, 0xF7, 0x45, 0xBA, 0xEA, 0xA3, 0x66, 0xC5, 0x5A, 0x08, 0x2D,
]);

/// The GUID identifying the SEV metadata GUID table entry.
///
/// This matches the SEV metadata GUID used in OVMF (dc886566-984a-4798-A75e-5585a7bf67cc).
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm>.
const SEV_MEATADATA_GUID: u128 = u128::from_le_bytes([
    0x66, 0x65, 0x88, 0xdc, 0x4a, 0x98, 0x98, 0x47, 0xA7, 0x5e, 0x55, 0x85, 0xa7, 0xbf, 0x67, 0xcc,
]);

/// The expected first 4 bytes of the SEV metadata section header.
const SEV_SECTION_SIGNATURE: &[u8] = b"ASEV";

/// The version of SEV metadata sections we expect to encounter.
const SEV_METADATA_VERSION: u32 = 1;

/// The contents of the Stage 0 firmware ROM image and its associated metadata.
pub struct Stage0Info {
    /// The bytes of the State 0 firmware ROM image.
    bytes: Vec<u8>,
    /// The start address of the firmware ROM in guest memory.
    pub start_address: PhysAddr,
    /// The start address of the legacy boot shadow of the firmware ROM in guest memory.
    pub legacy_start_address: PhysAddr,
    /// The offset into the firmware ROM image from where the legacy boot shadow starts.
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

    /// Gets the SEV-SNP specific pages defined in the firmware SEV metadata section entries.
    pub fn get_snp_pages(&self) -> Vec<SevMetadataPageInfo> {
        let sev_metadata_content = *self
            .parse_firmware_guid_table()
            .get(&SEV_MEATADATA_GUID)
            .expect("couldn't find SEV metadata entry in GUID table");
        assert_eq!(
            sev_metadata_content.len(),
            size_of::<u32>(),
            "invalid length for SEV metadata entry"
        );
        // We expect the SEV metadata entry in the GUID table to contain only 4 bytes that represent
        // the 32-bit unsigned little-endian encoding of the reverse offset from the end of the
        // firmware image to the start of the SEV metadata section.
        let mut sev_metadata_offset: u32 = 0;
        sev_metadata_offset
            .as_bytes_mut()
            .copy_from_slice(sev_metadata_content);
        let sev_metadata_offset = sev_metadata_offset as usize;
        trace!("SEV metadata offset: {}", sev_metadata_offset);
        assert!(
            sev_metadata_offset < self.bytes.len(),
            "invalid SEV metadata offset"
        );
        let sev_metadata_header_start = self.bytes.len() - sev_metadata_offset;
        let sev_metadata_header_end = sev_metadata_header_start + SEV_METADATA_HEADER_SIZE;
        let header = SevMetadataHeader::parse(
            &self.bytes[sev_metadata_header_start..sev_metadata_header_end],
        );
        trace!("SEV metadata entry count: {}", header.count);
        let metadata_entries_end = sev_metadata_header_start + header.length as usize;
        self.bytes[sev_metadata_header_end..metadata_entries_end]
            .chunks(SEV_METADATA_ENTRY_SIZE)
            .map(SevMetadataPageInfo::parse)
            .collect()
    }

    /// Parses the GUID table from the firmware image as a map.
    ///
    /// The GUID (represented as a u128) of each table entry is the key and the associated data of
    /// the entry is the value.
    fn parse_firmware_guid_table(&self) -> HashMap<u128, &[u8]> {
        let content = self.get_guid_table_content();
        let mut entry_end = content.len();
        let mut result = HashMap::new();
        while entry_end > GUID_TABLE_ENTRY_HEADER_SIZE {
            let GuidTableEntryHeader {
                guid: entry_guid,
                size: entry_size,
            } = GuidTableEntryHeader::parse(&content[..entry_end]);
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
    fn get_guid_table_content(&self) -> &[u8] {
        assert!(
            self.bytes.len() > GUID_TABLE_END_OFFSET + GUID_TABLE_ENTRY_HEADER_SIZE,
            "firmware ROM too small"
        );
        // We parse the GUID table from the end, starting at the footer.
        let table_end = self.bytes.len() - GUID_TABLE_END_OFFSET;
        trace!("GUID table end: {}", table_end);
        let GuidTableEntryHeader {
            guid: footer_guid,
            size: table_size,
        } = GuidTableEntryHeader::parse(&self.bytes[..table_end]);
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

    fn new(bytes: Vec<u8>) -> Self {
        let size = bytes.len();
        let start_address = FIRMWARE_TOP - size;
        let legacy_size = size.min(LEGACY_MAX_SIZE);
        let legacy_start_address = LEGACY_TOP - legacy_size;
        let legacy_offset = size - legacy_size;
        Self {
            bytes,
            start_address,
            legacy_start_address,
            legacy_offset,
        }
    }
}

/// Loads the Stage 0 firmware ROM image from the supplied path.
pub fn load_stage0(stage0_rom_path: PathBuf) -> anyhow::Result<Stage0Info> {
    let stage0_bytes =
        std::fs::read(stage0_rom_path).context("couldn't load stage0 firmware ROM image")?;
    debug!("Stage0 size: {}", stage0_bytes.len());

    let mut stage0_hasher = Sha256::new();
    stage0_hasher.update(&stage0_bytes);
    let stage0_sha256_digest = stage0_hasher.finalize();
    info!(
        "Stage0 digest: sha256:{}",
        hex::encode(stage0_sha256_digest)
    );
    Ok(Stage0Info::new(stage0_bytes))
}

/// Information about the pages specified in the firmware SEV metadata section entries.
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm>
pub struct SevMetadataPageInfo {
    pub start_address: PhysAddr,
    pub page_count: usize,
    pub page_type: PageType,
}

impl SevMetadataPageInfo {
    fn parse(bytes: &[u8]) -> Self {
        assert!(bytes.len() == SEV_METADATA_ENTRY_SIZE);
        let mut base: u32 = 0;
        base.as_bytes_mut().copy_from_slice(&bytes[0..4]);
        let start_address = PhysAddr::new(base as u64);
        assert_eq!(
            start_address,
            start_address.align_down(Size4KiB::SIZE),
            "invalid SEV metadata entry base address"
        );

        let mut size: u32 = 0;
        size.as_bytes_mut().copy_from_slice(&bytes[4..8]);
        assert_eq!(
            (size as u64) % Size4KiB::SIZE,
            0,
            "invalid SEV metadata entry size"
        );
        let page_count = (size as usize) / (Size4KiB::SIZE as usize);

        let mut page_type: u32 = 0;
        page_type.as_bytes_mut().copy_from_slice(&bytes[8..12]);
        trace!(
            "Metadata page entry: base: {}, size: {}, page_type: {}",
            base,
            size,
            page_type
        );
        let page_type = SevMetadataPageType::from_repr(page_type)
            .expect("invalid SEV metadata page type")
            .into();

        Self {
            start_address,
            page_count,
            page_type,
        }
    }
}

/// The page types used in the firmware SEV metadata section entries.
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm>
#[derive(Debug, FromRepr)]
#[repr(u32)]
enum SevMetadataPageType {
    Invalid = 0,
    Unmeasured = 1,
    Secrets = 2,
    Cpuid = 3,
}

impl From<SevMetadataPageType> for PageType {
    fn from(value: SevMetadataPageType) -> Self {
        match value {
            SevMetadataPageType::Invalid => panic!("invalid SEV metadata page type"),
            SevMetadataPageType::Cpuid => PageType::Cpuid,
            SevMetadataPageType::Secrets => PageType::Secrets,
            SevMetadataPageType::Unmeasured => PageType::Unmeasured,
        }
    }
}

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
        guid.as_bytes_mut()
            .copy_from_slice(&bytes[guid_start..guid_end]);
        let mut size: u16 = 0;
        let size_start = guid_start - size_of::<u16>();
        size.as_bytes_mut()
            .copy_from_slice(&bytes[size_start..guid_start]);
        Self { guid, size }
    }
}

/// The header of the SEV metadata section.
///
/// We validate the signature and version, but don't use it for anything else, so we don't need to
/// store their values in the struct.
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm>
struct SevMetadataHeader {
    length: u32,
    count: u32,
}

impl SevMetadataHeader {
    fn parse(bytes: &[u8]) -> Self {
        assert!(bytes.len() == SEV_METADATA_HEADER_SIZE);
        let mut signature: [u8; 4] = [0; 4];
        signature[..].copy_from_slice(&bytes[..4]);
        assert_eq!(
            signature, SEV_SECTION_SIGNATURE,
            "invalid signature for SEV metadata section"
        );
        let mut version: u32 = 0;
        version.as_bytes_mut().copy_from_slice(&bytes[8..12]);
        assert_eq!(
            version, SEV_METADATA_VERSION,
            "invalid version for SEV metadata section"
        );

        let mut length: u32 = 0;
        length.as_bytes_mut().copy_from_slice(&bytes[4..8]);
        let mut count: u32 = 0;
        count.as_bytes_mut().copy_from_slice(&bytes[12..16]);
        trace!("SEV metadata header: length:{}, count:{}", length, count);
        assert_eq!(
            length,
            count * (SEV_METADATA_ENTRY_SIZE as u32) + (SEV_METADATA_HEADER_SIZE as u32),
            "invalid length or count in SEV metadata section"
        );
        Self { length, count }
    }
}
