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

use core::{ffi::CStr, fmt::Debug};

use sha2::Sha256;

use crate::{
    acpi::{
        commands::{
            add_pci_root_stage1::PCI_ROOT_STAGE1_ALLOWLIST_COUNT, Invoke, Pad, RomfileName,
        },
        files::Files,
    },
    fw_cfg::Firmware,
    pci::PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT,
};

const PCI_ROOT_ALLOWLIST_COUNT: usize = PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT * 2;
const PCI_ROOT_STAGE2_ALLOWLIST_COUNT: usize =
    PCI_ROOT_ALLOWLIST_COUNT - PCI_ROOT_STAGE1_ALLOWLIST_COUNT;

#[repr(C)]
#[derive(Copy, Clone)]
pub struct AddPciRootStage2 {
    file: RomfileName,
    allowlist_offsets: [u32; PCI_ROOT_STAGE2_ALLOWLIST_COUNT],
    bus_index: u8,
    _padding: [u8; 8],
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
        _files: &mut F,
        _fwcfg: &mut FW,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        log::error!(
            "AddPciRootStage2 not implemented; ACPI tables may be broken! Command: {:?}",
            self
        );
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
