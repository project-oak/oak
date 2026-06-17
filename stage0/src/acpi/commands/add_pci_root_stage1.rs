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

use core::{ffi::CStr, fmt::Debug, iter::zip};

use sha2::Sha256;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

use crate::{
    acpi::{
        commands::{Invoke, Pad, RomfileName},
        files::Files,
    },
    fw_cfg::Firmware,
    pci::{PciWindows, read_pci_crs_allowlist},
};

pub const PCI_ROOT_STAGE1_ALLOWLIST_OFFSET_COUNT: usize = 4;

#[repr(C)]
#[derive(Copy, Clone, Debug, FromBytes, IntoBytes, KnownLayout, Immutable)]
pub struct AllowlistOffset {
    pub start: u32,
    pub end: u32,
}
static_assertions::assert_eq_size!(AllowlistOffset, u64);

#[repr(C)]
#[derive(Copy, Clone, FromBytes, IntoBytes, KnownLayout, Immutable)]
pub struct AddPciRootStage1 {
    file: RomfileName,

    pci32_start_offset: u32,
    pci32_end_offset: u32,
    pci64_valid_offset: u32,
    pci64_start_offset: u32,
    pci64_end_offset: u32,
    pci64_length_offset: u32,
    pci16_io_start_offset: u32,
    pci16_io_end_offset: u32,
    // 8 offsets in 4 pairs.
    allowlist_offsets: [AllowlistOffset; PCI_ROOT_STAGE1_ALLOWLIST_OFFSET_COUNT],
    bus_index: u8,
    _reserved: [u8; 3],
}
static_assertions::assert_eq_size!(AddPciRootStage1, Pad);

impl AddPciRootStage1 {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }

    /// Builds a command targeting `file` whose 32-bit window start is written at
    /// `pci32_start_offset`; all other offsets stay zero. Test-only.
    #[cfg(test)]
    pub fn new(file: &str, pci32_start_offset: u32) -> Self {
        let mut cmd = <Self as zerocopy::FromZeros>::new_zeroed();
        cmd.file[..file.len()].copy_from_slice(file.as_bytes());
        cmd.pci32_start_offset = pci32_start_offset;
        cmd
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddPciRootStage1 {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
        pci_windows: Option<&PciWindows>,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        log::warn!("AddPciRootStage1 untested; command: {:?}", self);
        let file = files.get_file_mut(self.file())?;

        if self.bus_index != 0 {
            return Err("AddPciRootStage1: only bus 0 supported for now");
        }

        let file_len = file.len();
        let write_fits = |offset: u32, size: usize| offset as usize + size <= file_len;
        if !write_fits(self.pci32_start_offset, size_of::<u32>())
            || !write_fits(self.pci32_end_offset, size_of::<u32>())
            || !write_fits(self.pci64_valid_offset, size_of::<u8>())
            || !write_fits(self.pci64_start_offset, size_of::<u64>())
            || !write_fits(self.pci64_end_offset, size_of::<u64>())
            || !write_fits(self.pci64_length_offset, size_of::<u64>())
            || !write_fits(self.pci16_io_start_offset, size_of::<u16>())
            || !write_fits(self.pci16_io_end_offset, size_of::<u16>())
            || self.allowlist_offsets.iter().any(|o| {
                !write_fits(o.start, size_of::<u32>()) || !write_fits(o.end, size_of::<u32>())
            })
        {
            return Err("AddPciRootStage1 invalid; offsets would overflow file");
        }

        let data = pci_windows.ok_or("no PCI holes for AddPciRootStage1 to add")?;

        file[self.pci32_start_offset as usize
            ..(self.pci32_start_offset as usize + size_of_val(&data.pci_window_32.start))]
            .copy_from_slice(&data.pci_window_32.start.to_le_bytes());
        file[self.pci32_end_offset as usize
            ..(self.pci32_end_offset as usize + size_of_val(&data.pci_window_32.end))]
            .copy_from_slice(&data.pci_window_32.end.to_le_bytes());

        if data.pci_window_64.start != 0 {
            let len = data.pci_window_64.end - data.pci_window_64.start;
            file[self.pci64_valid_offset as usize] = 1;
            file[self.pci64_start_offset as usize
                ..(self.pci64_start_offset as usize + size_of_val(&data.pci_window_64.start))]
                .copy_from_slice(&data.pci_window_64.start.to_le_bytes());
            file[self.pci64_end_offset as usize
                ..(self.pci64_end_offset as usize + size_of_val(&data.pci_window_64.end))]
                .copy_from_slice(&data.pci_window_64.end.to_le_bytes());
            file[self.pci64_length_offset as usize
                ..(self.pci64_length_offset as usize + size_of_val(&len))]
                .copy_from_slice(&len.to_le_bytes());
        } else {
            file[self.pci64_valid_offset as usize] = 0;
        }

        file[self.pci16_io_start_offset as usize
            ..(self.pci16_io_start_offset as usize + size_of::<u16>())]
            .copy_from_slice(&data.pci_window_16.start.to_le_bytes());
        file[self.pci16_io_end_offset as usize
            ..(self.pci16_io_end_offset as usize + size_of::<u16>())]
            .copy_from_slice(&data.pci_window_16.end.to_le_bytes());

        let crs_allowlist = read_pci_crs_allowlist(fwcfg)?.unwrap_or_default();
        log::debug!("PCI CRS allowlist: {:?}", crs_allowlist);

        // This command contains the first 4 offsets (8 entries in total)
        for (allowlist_offset, crs_allowlist) in zip(self.allowlist_offsets, crs_allowlist) {
            let offset_start = allowlist_offset.start as usize;
            let offset_end = allowlist_offset.end as usize;

            file[offset_start..offset_start + size_of::<u32>()]
                .copy_from_slice(&crs_allowlist.address.to_le_bytes());
            let end = crs_allowlist.address + crs_allowlist.length - 1;
            file[offset_end..offset_end + size_of::<u32>()].copy_from_slice(&end.to_le_bytes());
        }

        Ok(())
    }
}

impl Debug for AddPciRootStage1 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AddPciRootStage1")
            .field("file", &self.file())
            .field("pci32_start_offset", &self.pci32_start_offset)
            .field("pci32_end_offset", &self.pci32_end_offset)
            .field("pci64_valid_offset", &self.pci64_valid_offset)
            .field("pci64_start_offset", &self.pci64_start_offset)
            .field("pci64_end_offset", &self.pci64_end_offset)
            .field("pci64_length_offset", &self.pci64_length_offset)
            .field("pci16_io_start_offset", &self.pci16_io_start_offset)
            .field("pci16_io_end_offset", &self.pci16_io_end_offset)
            .field("allowlist_offsets", &self.allowlist_offsets)
            .field("bus_index", &self.bus_index)
            .finish()
    }
}
