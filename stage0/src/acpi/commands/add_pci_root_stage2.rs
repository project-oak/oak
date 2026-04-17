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

use crate::{
    acpi::{
        commands::{
            Invoke, Pad, RomfileName,
            add_pci_root_stage1::{AllowlistOffset, PCI_ROOT_STAGE1_ALLOWLIST_OFFSET_COUNT},
        },
        files::Files,
    },
    fw_cfg::Firmware,
    pci::{PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT, PciWindows, read_pci_crs_allowlist},
};

const PCI_ROOT_STAGE2_ALLOWLIST_OFFSET_COUNT: usize =
    PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT - PCI_ROOT_STAGE1_ALLOWLIST_OFFSET_COUNT;

#[repr(C)]
#[derive(Copy, Clone)]
pub struct AddPciRootStage2 {
    file: RomfileName,
    // 4 of them in Stage1; rest (11-4) here.
    allowlist_offsets: [AllowlistOffset; PCI_ROOT_STAGE2_ALLOWLIST_OFFSET_COUNT],
    bus_index: u8,
    _padding: [u8; 11],
}
static_assertions::assert_eq_size!(AddPciRootStage2, Pad);

impl AddPciRootStage2 {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddPciRootStage2 {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
        _pci_windows: Option<&PciWindows>,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        log::warn!("AddPciRootStage2 not tested; ACPI tables may be broken! Command: {:?}", self);
        let file = files.get_file_mut(self.file())?;

        if self.bus_index != 0 {
            return Err("AddPciRootStage2: only bus 0 supported for now");
        }
        let crs_allowlist = read_pci_crs_allowlist(fwcfg)?.unwrap_or_default();
        log::debug!("PCI CRS allowlist: {:?}", crs_allowlist);

        // The first 4 entries (8 offsets) are consumed in ADD_PCI_ROOT_STAGE1.
        for (allowlist_offset, crs_allowlist) in
            zip(self.allowlist_offsets, crs_allowlist[4..].iter())
        {
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

impl Debug for AddPciRootStage2 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AddPciRootStage2")
            .field("file", &self.file())
            .field("allowlist_offsets", &self.allowlist_offsets)
            .field("bus_index", &self.bus_index)
            .finish()
    }
}
