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

use std::{mem::size_of, path::PathBuf};

use anyhow::Context;
use log::{debug, info, trace};
use sha2::{Digest, Sha256};
use stage0_parsing::Stage0Info;
use strum::FromRepr;
use x86_64::{
    PhysAddr,
    structures::paging::{PageSize, Size4KiB},
};
use zerocopy::IntoBytes;

use crate::page::PageType;

/// The size of the SEV metadata section header.
const SEV_METADATA_HEADER_SIZE: usize = 16;

/// The size of the SEV metadata section entry.
const SEV_METADATA_ENTRY_SIZE: usize = 12;

/// The GUID identifying the SEV metadata GUID table entry.
///
/// This matches the SEV metadata GUID used in OVMF
/// (dc886566-984a-4798-A75e-5585a7bf67cc).
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm>.
const SEV_MEATADATA_GUID: u128 = u128::from_le_bytes([
    0x66, 0x65, 0x88, 0xdc, 0x4a, 0x98, 0x98, 0x47, 0xA7, 0x5e, 0x55, 0x85, 0xa7, 0xbf, 0x67, 0xcc,
]);

/// The GUID identifying the SEV ES reset block GUID table entry.
///
/// This matches the SEV ES reset block GUID used in OVMF
/// (00f771de-1a7e-4fcb-890e-68c77e2fb44e).
///
/// See <https://github.com/tianocore/edk2/blob/fff6d81270b57ee786ea18ad74f43149b9f03494/OvmfPkg/ResetVector/Ia16/ResetVectorVtf0.asm>.
const SEV_ES_RESET_GUID: u128 = u128::from_le_bytes([
    0xde, 0x71, 0xf7, 0x00, 0x7e, 0x1a, 0xcb, 0x4f, 0x89, 0x0e, 0x68, 0xc7, 0x7e, 0x2f, 0xb4, 0x4e,
]);

/// The expected first 4 bytes of the SEV metadata section header.
const SEV_SECTION_SIGNATURE: &[u8] = b"ASEV";

/// The version of SEV metadata sections we expect to encounter.
const SEV_METADATA_VERSION: u32 = 1;

pub trait SnpRomParsing {
    /// Gets the SEV-SNP specific pages defined in the firmware SEV metadata
    /// section entries.
    fn get_snp_pages(&self) -> Vec<SevMetadataPageInfo>;
    /// Gets the SEV-ES reset block from the firmware image.
    fn get_sev_es_reset_block(&self) -> SevEsResetBlock;
}

impl SnpRomParsing for Stage0Info {
    fn get_snp_pages(&self) -> Vec<SevMetadataPageInfo> {
        let sev_metadata_content = *self
            .parse_firmware_guid_table()
            .get(&SEV_MEATADATA_GUID)
            .expect("couldn't find SEV metadata entry in GUID table");
        assert_eq!(
            sev_metadata_content.len(),
            size_of::<u32>(),
            "invalid length for SEV metadata entry"
        );
        // We expect the SEV metadata entry in the GUID table to contain only 4 bytes
        // that represent the 32-bit unsigned little-endian encoding of the
        // reverse offset from the end of the firmware image to the start of the
        // SEV metadata section.
        let mut sev_metadata_offset: u32 = 0;
        sev_metadata_offset.as_mut_bytes().copy_from_slice(sev_metadata_content);
        let sev_metadata_offset = sev_metadata_offset as usize;
        trace!("SEV metadata offset: {}", sev_metadata_offset);
        assert!(sev_metadata_offset < self.bytes.len(), "invalid SEV metadata offset");
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

    fn get_sev_es_reset_block(&self) -> SevEsResetBlock {
        let sev_es_reset_block_content = *self
            .parse_firmware_guid_table()
            .get(&SEV_ES_RESET_GUID)
            .expect("couldn't find SEV-ES reset block entry in GUID table");
        assert_eq!(
            sev_es_reset_block_content.len(),
            size_of::<u32>(),
            "invalid length for SEV-ES reset block entry"
        );
        // We expect the SEV-ES reset block entry in the GUID table to contain only 4
        // bytes that represent the 32-bit unsigned little-endian encoding of
        // the reset address.
        let mut sev_es_reset_address: u32 = 0;
        sev_es_reset_address.as_mut_bytes().copy_from_slice(sev_es_reset_block_content);
        sev_es_reset_address.into()
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
    info!("Stage0 digest: sha256:{}", hex::encode(stage0_sha256_digest));
    Ok(Stage0Info::new(stage0_bytes))
}

/// Information about the pages specified in the firmware SEV metadata section
/// entries.
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
        base.as_mut_bytes().copy_from_slice(&bytes[0..4]);
        let start_address = PhysAddr::new(base as u64);
        assert_eq!(
            start_address,
            start_address.align_down(Size4KiB::SIZE),
            "invalid SEV metadata entry base address"
        );

        let mut size: u32 = 0;
        size.as_mut_bytes().copy_from_slice(&bytes[4..8]);
        assert_eq!((size as u64) % Size4KiB::SIZE, 0, "invalid SEV metadata entry size");
        let page_count = (size as usize) / (Size4KiB::SIZE as usize);

        let mut page_type: u32 = 0;
        page_type.as_mut_bytes().copy_from_slice(&bytes[8..12]);
        trace!("Metadata page entry: base: {}, size: {}, page_type: {}", base, size, page_type);
        let page_type = SevMetadataPageType::from_repr(page_type)
            .expect("invalid SEV metadata page type")
            .into();

        Self { start_address, page_count, page_type }
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

/// The instruction pointer and code segment base that will be set when a
/// non-boot vCPU is reset.
pub struct SevEsResetBlock {
    pub rip: u64,
    pub segment_base: u64,
}

impl From<u32> for SevEsResetBlock {
    fn from(value: u32) -> Self {
        // The instruction pointer is the two least significant bytes of the address.
        let rip = (value & 0x0000ffff) as u64;
        // The code segment base is the address with the two least significant bytes
        // zeroed out.
        let segment_base = (value & 0xffff0000) as u64;
        Self { rip, segment_base }
    }
}

/// The header of the SEV metadata section.
///
/// We validate the signature and version, but don't use it for anything else,
/// so we don't need to store their values in the struct.
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
        assert_eq!(signature, SEV_SECTION_SIGNATURE, "invalid signature for SEV metadata section");
        let mut version: u32 = 0;
        version.as_mut_bytes().copy_from_slice(&bytes[8..12]);
        assert_eq!(version, SEV_METADATA_VERSION, "invalid version for SEV metadata section");

        let mut length: u32 = 0;
        length.as_mut_bytes().copy_from_slice(&bytes[4..8]);
        let mut count: u32 = 0;
        count.as_mut_bytes().copy_from_slice(&bytes[12..16]);
        trace!("SEV metadata header: length:{}, count:{}", length, count);
        assert_eq!(
            length,
            count * (SEV_METADATA_ENTRY_SIZE as u32) + (SEV_METADATA_HEADER_SIZE as u32),
            "invalid length or count in SEV metadata section"
        );
        Self { length, count }
    }
}
