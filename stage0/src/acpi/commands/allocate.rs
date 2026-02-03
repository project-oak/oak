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
};

use sha2::{Digest, Sha256};
#[cfg(test)]
use zerocopy::{Immutable, IntoBytes};

use super::{Invoke, Pad, RomfileName};
use crate::{
    acpi::{Zone, files::Files},
    fw_cfg::Firmware,
    pci::PciWindows,
};

/// COMMAND_ALLOCATE - allocate a table from `file` subject to `align` alignment
/// (must be power of
/// 2) and `zone` (can be HIGH or FSEG) requirements.
///
/// Must appear exactly once for each file, and before this file is referenced
/// by any other command.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Allocate {
    file: RomfileName,
    align: u32,
    zone: u8,
    _padding: [u8; 63],
}
static_assertions::assert_eq_size!(Allocate, Pad);

impl Allocate {
    #[cfg(test)]
    pub fn new<T: IntoBytes + Immutable + ?Sized>(file: &T, align: u32, zone: Zone) -> Self {
        let mut cmd = Self {
            file: [0; super::ROMFILE_LOADER_FILESZ],
            align,
            zone: zone as u8,
            _padding: [0; 63],
        };
        cmd.file[..file.as_bytes().len()].copy_from_slice(file.as_bytes());

        cmd
    }

    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }

    pub fn zone(&self) -> Option<Zone> {
        Zone::from_repr(self.zone)
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for Allocate {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
        _pci_windows: Option<&PciWindows>,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        let file = fwcfg.find(self.file()).unwrap();

        let layout = core::alloc::Layout::from_size_align(file.size(), self.align as usize)
            .map_err(|_| "invalid file layout requested")?;

        let buf = files.allocate(
            self.file(),
            layout,
            self.zone().ok_or("Invalid file allocation zone")?,
        )?;

        fwcfg.read_file(&file, buf)?;
        acpi_digest.update(buf);
        Ok(())
    }
}

impl Debug for Allocate {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("Allocate")
            .field("file", &self.file())
            .field("align", &self.align)
            .field("zone", &self.zone())
            .finish()
    }
}
