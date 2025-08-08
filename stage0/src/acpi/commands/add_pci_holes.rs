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

use core::{
    ffi::CStr,
    fmt::{Debug, Formatter, Result as FmtResult},
    mem::size_of_val,
};

use sha2::Sha256;

use super::{Invoke, Pad, RomfileName};
use crate::{acpi::files::Files, fw_cfg::Firmware, pci::PciWindows};

#[repr(C)]
#[derive(Copy, Clone)]
pub struct AddPciHoles {
    file: RomfileName,
    pci_start_offset_32: u32,
    pci_end_offset_32: u32,
    pci_valid_offset_64: u32,
    pci_start_offset_64: u32,
    pci_end_offset_64: u32,
    pci_length_offset_64: u32,
    _padding: [u8; 44],
}
static_assertions::assert_eq_size!(AddPciHoles, Pad);

impl AddPciHoles {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddPciHoles {
    fn invoke(
        &self,
        files: &mut F,
        _fwcfg: &mut FW,
        pci_windows: Option<&PciWindows>,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        let file = files.get_file_mut(self.file())?;

        if file.len() < self.pci_start_offset_32 as usize
            || file.len() - 4 < self.pci_start_offset_32 as usize
            || file.len() < self.pci_end_offset_32 as usize
            || file.len() - 4 < self.pci_end_offset_32 as usize
            || file.len() < self.pci_valid_offset_64 as usize
            || file.len() - 1 < self.pci_valid_offset_64 as usize
            || file.len() < self.pci_start_offset_64 as usize
            || file.len() - 8 < self.pci_start_offset_64 as usize
            || file.len() < self.pci_end_offset_64 as usize
            || file.len() - 8 < self.pci_end_offset_64 as usize
            || file.len() < self.pci_length_offset_64 as usize
            || file.len() - 8 < self.pci_length_offset_64 as usize
            || file.len() < (4 + 4 + 1 + 8 + 8 + 8)
        {
            return Err("ADD_PCI_HOLES invalid; offsets would overflow file");
        }

        let data = pci_windows.ok_or("no PCI holes for AddPciHoles to add")?;

        // 32 bit
        file[self.pci_start_offset_32 as usize
            ..(self.pci_start_offset_32 as usize + size_of_val(&data.pci_window_32.start))]
            .copy_from_slice(&data.pci_window_32.start.to_le_bytes());
        file[self.pci_end_offset_32 as usize
            ..(self.pci_end_offset_32 as usize + size_of_val(&data.pci_window_32.end))]
            .copy_from_slice(&data.pci_window_32.end.to_le_bytes());

        // 64-bit
        if data.pci_window_64.start != 0 {
            let len = data.pci_window_64.end - data.pci_window_64.start;
            file[self.pci_valid_offset_64 as usize] = 1;
            file[self.pci_start_offset_64 as usize
                ..(self.pci_start_offset_64 as usize + size_of_val(&data.pci_window_64.start))]
                .copy_from_slice(&data.pci_window_64.start.to_le_bytes());
            file[self.pci_end_offset_64 as usize
                ..(self.pci_end_offset_64 as usize + size_of_val(&data.pci_window_64.end))]
                .copy_from_slice(&data.pci_window_64.end.to_le_bytes());
            file[self.pci_length_offset_64 as usize
                ..(self.pci_length_offset_64 as usize + size_of_val(&len))]
                .copy_from_slice(&len.to_le_bytes());
        } else {
            file[self.pci_valid_offset_64 as usize] = 0;
        }

        Ok(())
    }
}

impl Debug for AddPciHoles {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("AddPciHoles")
            .field("file", &self.file())
            .field("pci_start_offset_32", &self.pci_start_offset_32)
            .field("pci_end_offset_32", &self.pci_end_offset_32)
            .field("pci_valid_offset_64", &self.pci_valid_offset_64)
            .field("pci_start_offset_64", &self.pci_start_offset_64)
            .field("pci_end_offset_64", &self.pci_end_offset_64)
            .field("pci_length_offset_64", &self.pci_length_offset_64)
            .finish()
    }
}
