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

use sha2::Sha256;
#[cfg(test)]
use zerocopy::{Immutable, IntoBytes};

use super::{Invoke, Pad, RomfileName};
use crate::{acpi::files::Files, fw_cfg::Firmware};

/// COMMAND_ADD_CHECKSUM - calculate checksum of the range specified by `start`
/// and `length` fields, and then add the value at `offset`.
///
/// Checksum simply sums -X for each byte X in the range using 8-bit math (or in
/// our case, we just sum together all the numbers and subtract in the end.)
///
/// See `bios_linker_loader_add_checksum()` in QEMU
/// `hw/acpi/bios-linker-loader.c` for the best available documentation.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct AddChecksum {
    file: RomfileName,
    /// Location of the checksum to be patched within the file, relative to the
    /// start of the file
    offset: u32,

    /// Start of the data in the file to checksum, relative to the start of the
    /// file
    start: u32,

    /// Size of the data in the file to checksum, offset from `start`
    length: u32,
    _padding: [u8; 56],
}
static_assertions::assert_eq_size!(AddChecksum, Pad);

impl AddChecksum {
    #[cfg(test)]
    pub fn new<T: IntoBytes + Immutable + ?Sized>(
        file: &T,
        offset: u32,
        start: u32,
        length: u32,
    ) -> Self {
        let mut cmd = Self {
            file: [0; super::ROMFILE_LOADER_FILESZ],
            offset,
            start,
            length,
            _padding: [0; 56],
        };
        cmd.file[..file.as_bytes().len()].copy_from_slice(file.as_bytes());

        cmd
    }
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }

    fn checksum(buf: &[u8]) -> u8 {
        buf.iter().fold(0, |checksum, &x| checksum.wrapping_add(x))
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddChecksum {
    fn invoke(
        &self,
        files: &mut F,
        _fwcfg: &mut FW,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        let file = files.get_file_mut(self.file())?;

        if self.start as usize > file.len()
            || (self.start + self.length) as usize > file.len()
            || self.offset as usize >= file.len()
        {
            return Err("COMMAND_ADD_CHECKSUM invalid; read or write would overflow file");
        }

        let checksum =
            AddChecksum::checksum(&file[self.start as usize..(self.start + self.length) as usize]);
        let val = file.get_mut(self.offset as usize).unwrap();
        *val = val.wrapping_sub(checksum);
        Ok(())
    }
}

impl Debug for AddChecksum {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("AddChecksum")
            .field("file", &self.file())
            .field("offset", &self.offset)
            .field("start", &self.start)
            .field("length", &self.length)
            .finish()
    }
}
