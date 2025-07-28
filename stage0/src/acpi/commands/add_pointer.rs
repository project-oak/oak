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
use zerocopy::Immutable;
use zerocopy::IntoBytes;

use super::{Invoke, Pad, RomfileName};
use crate::{acpi::files::Files, fw_cfg::Firmware};

/// COMMAND_ADD_POINTER - patch the table (originating from `dest_file`) at
/// `offset`, by adding a pointer to the table originating from `src_file`.
///
/// 1,2,4 or 8 byte unsigned addition is used depending on `size`.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct AddPointer {
    dest_file: RomfileName,
    src_file: RomfileName,
    offset: u32,
    size: u8,
    _padding: [u8; 7],
}
static_assertions::assert_eq_size!(AddPointer, Pad);

impl AddPointer {
    #[cfg(test)]
    pub fn new<T: IntoBytes + Immutable + ?Sized>(
        dest_file: &T,
        src_file: &T,
        offset: u32,
        size: u8,
    ) -> Self {
        let mut cmd = Self {
            dest_file: [0; super::ROMFILE_LOADER_FILESZ],
            src_file: [0; super::ROMFILE_LOADER_FILESZ],
            offset,
            size,
            _padding: [0; 7],
        };
        cmd.dest_file[..dest_file.as_bytes().len()].copy_from_slice(dest_file.as_bytes());
        cmd.src_file[..src_file.as_bytes().len()].copy_from_slice(src_file.as_bytes());

        cmd
    }

    pub fn dest_file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.dest_file).unwrap()
    }

    pub fn src_file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.src_file).unwrap()
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddPointer {
    fn invoke(
        &self,
        files: &mut F,
        _fwcfg: &mut FW,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        let src_file_ptr = files.get_file(self.src_file())?.as_ptr();
        let dest_file = files.get_file_mut(self.dest_file())?;

        if self.offset as usize + self.size as usize > dest_file.len() {
            return Err("Write for COMMAND_ADD_POINTER would overflow destination file");
        }
        if self.size > 8 || !self.size.is_power_of_two() {
            return Err("COMMAND_ADD_POINTER has invalid size");
        }
        let mut pointer = 0u64;
        pointer.as_mut_bytes()[..self.size as usize].copy_from_slice(
            &dest_file[self.offset as usize..(self.offset + self.size as u32) as usize],
        );
        pointer += src_file_ptr as u64;
        dest_file[self.offset as usize..(self.offset + self.size as u32) as usize]
            .copy_from_slice(&pointer.as_bytes()[..self.size as usize]);

        Ok(())
    }
}

impl Debug for AddPointer {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("AddPointer")
            .field("dest_file", &self.dest_file())
            .field("src_file", &self.src_file())
            .field("offset", &self.offset)
            .field("size", &self.size)
            .finish()
    }
}
