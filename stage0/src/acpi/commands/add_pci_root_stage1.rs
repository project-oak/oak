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

use crate::acpi::{
    commands::{Invoke, Pad, RomfileName},
    files::Files,
    Firmware,
};

pub const PCI_ROOT_STAGE1_ALLOWLIST_COUNT: usize = 8;

#[repr(C)]
#[derive(Copy, Clone)]
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
    allowlist_offsets: [u32; PCI_ROOT_STAGE1_ALLOWLIST_COUNT],
    bus_index: u8,
}
static_assertions::assert_eq_size!(AddPciRootStage1, Pad);

impl AddPciRootStage1 {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddPciRootStage1 {
    fn invoke(
        &self,
        _files: &mut F,
        _fwcfg: &mut FW,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        log::error!(
            "AddPciRootStage1 not implemented; ACPI tables may be broken! Command: {:?}",
            self
        );
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
