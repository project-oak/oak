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

// These data structures (and constants) are derived from qemu/hw/acpi/bios-linker-loader.c that
// defines the interface.

use crate::{acpi_tables::Rsdp, fw_cfg::FwCfg};
use core::{
    ffi::CStr,
    fmt::{Debug, Formatter, Result as FmtResult},
    mem::{size_of, zeroed, MaybeUninit},
};
use sha2::{Digest, Sha256};
use strum::FromRepr;
use zerocopy::AsBytes;

// RSDP has to be within the first 1 KiB of EBDA, so we treat it separately. The full size of EBDA
// is 128 KiB, but let's reserve the whole 1 KiB for the RSDP.
pub const EBDA_SIZE: usize = 127 * 1024;
#[link_section = ".ebda.rsdp"]
static mut RSDP: MaybeUninit<Rsdp> = MaybeUninit::uninit();
#[link_section = ".ebda"]
pub static mut EBDA: MaybeUninit<[u8; EBDA_SIZE]> = MaybeUninit::uninit();

// Safety: we include a nul byte at the end of the string, and that is the only nul byte.
const TABLE_LOADER_FILE_NAME: &CStr =
    unsafe { CStr::from_bytes_with_nul_unchecked(b"etc/table-loader\0") };
const RSDP_FILE_NAME_SUFFIX: &str = "acpi/rsdp";
const ACPI_TABLES_FILE_NAME_SUFFIX: &str = "acpi/tables";

const ROMFILE_LOADER_FILESZ: usize = 56;

type RomfileName = [u8; ROMFILE_LOADER_FILESZ];

fn get_file(name: &CStr) -> Result<&'static mut [u8], &'static str> {
    // Safety: we do not have concurrent threads so accessing the static is safe, and even if
    // Allocate has not been called yet, all values are valid for an [u8].
    let name = name.to_str().map_err(|_| "invalid file name")?;
    if name.ends_with(RSDP_FILE_NAME_SUFFIX) {
        Ok(unsafe { RSDP.assume_init_mut().as_bytes_mut() })
    } else if name.ends_with(ACPI_TABLES_FILE_NAME_SUFFIX) {
        Ok(unsafe { EBDA.assume_init_mut() })
    } else {
        Err("Unsupported file in table-loader")
    }
}

#[repr(u32)]
#[derive(Debug, FromRepr)]
enum CommandTag {
    Allocate = 1,
    AddPointer = 2,
    AddChecksum = 3,
    WritePointer = 4,
}

#[repr(u8)]
#[derive(Debug, FromRepr)]
enum Zone {
    High = 1,
    FSeg = 2,
}

/// COMMAND_ALLOCATE - allocate a table from `file` subject to `align` alignment (must be power of
/// 2) and `zone` (can be HIGH or FSEG) requirements.
///
/// Must appear exactly once for each file, and before this file is referenced by any other command.
#[repr(C)]
#[derive(Copy, Clone)]
struct Allocate {
    file: RomfileName,
    align: u32,
    zone: u8,
    _padding: [u8; 60],
}
static_assertions::assert_eq_size!(Allocate, Pad);

impl Allocate {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }

    pub fn zone(&self) -> Option<Zone> {
        Zone::from_repr(self.zone)
    }

    fn invoke(&self, fwcfg: &mut FwCfg, acpi_digest: &mut Sha256) -> Result<(), &'static str> {
        let file = fwcfg.find(self.file()).unwrap();
        let name = self.file().to_str().map_err(|_| "invalid file name")?;

        if name.ends_with(RSDP_FILE_NAME_SUFFIX) {
            // ACPI 1.0 RSDP is 20 bytes, ACPI 2.0 RSDP is 36 bytes.
            // We don't really care which version we're dealing with, as long as the data structure
            // is one of the two.
            if file.size() > size_of::<Rsdp>() || (file.size() != 20 && file.size() != 36) {
                return Err("RSDP doesn't match expected size");
            }

            // Safety: we do not have concurrent threads so accessing the static is safe.
            let buf = unsafe { RSDP.write(zeroed()) };

            // Sanity checks.
            if (buf as *const _ as u64) < 0x80000 || (buf as *const _ as u64) > 0x81000 {
                log::error!("RSDP address: {:p}", buf);
                return Err("RSDP address is not within the first 1 KiB of EBDA");
            }
            if (buf as *const _ as u64) % self.align as u64 != 0 {
                return Err("RSDP address not aligned properly");
            }

            fwcfg.read_file(&file, buf.as_bytes_mut())?;
            acpi_digest.update(buf.as_bytes());
            Ok(())
        } else if name.ends_with(ACPI_TABLES_FILE_NAME_SUFFIX) {
            // Safety: we do not have concurrent threads so accessing the static is safe.
            let buf = unsafe { EBDA.write(zeroed()) };

            if (buf.as_ptr() as *const _ as u64) % self.align as u64 != 0 {
                log::error!(
                    "ACPI tables address: {:p}, required alignment: {}",
                    buf,
                    self.align
                );
                return Err("ACPI tables address not aligned properly");
            }
            fwcfg.read_file(&file, buf)?;
            acpi_digest.update(buf);
            Ok(())
        } else {
            Err("Unsupported file in table-loader")
        }
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

/// COMMAND_ADD_POINTER - patch the table (originating from `dest_file`) at `offset`, by adding a
/// pointer to the table originating from `src_file`.
///
/// 1,2,4 or 8 byte unsigned addition is used depending on `size`.
#[repr(C)]
#[derive(Copy, Clone)]
struct AddPointer {
    dest_file: RomfileName,
    src_file: RomfileName,
    offset: u32,
    size: u8,
    _padding: [u8; 6],
}
static_assertions::assert_eq_size!(AddPointer, Pad);

impl AddPointer {
    pub fn dest_file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.dest_file).unwrap()
    }

    pub fn src_file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.src_file).unwrap()
    }

    fn invoke(&self) -> Result<(), &'static str> {
        let dest_file = get_file(self.dest_file())?;
        let src_file = get_file(self.src_file())?;

        if self.offset as usize + self.size as usize > dest_file.len() {
            return Err("Write for COMMAND_ADD_POINTER would overflow destination file");
        }
        if self.size > 8 || !self.size.is_power_of_two() {
            log::debug!("size: {}", self.size);
            return Err("COMMAND_ADD_POINTER has invalid size");
        }
        let mut pointer = 0u64;
        pointer.as_bytes_mut()[..self.size as usize].copy_from_slice(
            &dest_file[self.offset as usize..(self.offset + self.size as u32) as usize],
        );
        pointer += src_file.as_ptr() as u64;
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

/// COMMAND_ADD_CHECKSUM - calculate checksum of the range specified by `start` and `length` fields,
/// and then add the value at `offset`.
///
/// Checksum simply sums -X for each byte X in the range using 8-bit math (or in our case, we just
/// sum together all the numbers and subtract in the end.)
#[repr(C)]
#[derive(Copy, Clone)]
struct AddChecksum {
    file: RomfileName,
    offset: u32,
    start: u32,
    length: u32,
    _padding: [u8; 54],
}
static_assertions::assert_eq_size!(AddChecksum, Pad);

impl AddChecksum {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }

    fn invoke(&self) -> Result<(), &'static str> {
        let file = get_file(self.file())?;

        if self.start as usize > file.len()
            || (self.start + self.length) as usize > file.len()
            || self.offset as usize > file.len()
        {
            return Err("COMMAND_ADD_CHECKSUM invalid; read or write would overflow file");
        }

        let checksum =
            AddChecksum::checksum(&file[self.start as usize..(self.start + self.length) as usize]);
        *file.get_mut(self.offset as usize).unwrap() -= checksum;
        Ok(())
    }

    fn checksum(buf: &[u8]) -> u8 {
        buf.iter().fold(0, |checksum, &x| checksum.wrapping_add(x))
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

/// COMMAND_WRITE_POINTER - write the fw_cfg file (originating from `dest_file`) at `offset`, by
/// adding a pointer to `src_offset` within the table originating from `src_file`.
///
/// 1,2,4 or 8 byte unsigned addition is used depending on `size`.
#[repr(C)]
#[derive(Copy, Clone)]
struct WritePointer {
    dest_file: RomfileName,
    src_file: RomfileName,
    dst_offset: u32,
    src_offset: u32,
    size: u8,
}
static_assertions::assert_eq_size!(WritePointer, Pad);

impl WritePointer {
    pub fn dest_file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.dest_file).unwrap()
    }

    pub fn src_file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.src_file).unwrap()
    }

    fn invoke(&self) -> Result<(), &'static str> {
        log::debug!("{:?}", self);
        Err("COMMAND_WRITE_POINTER is not supported")
    }
}

impl Debug for WritePointer {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("WritePointer")
            .field("dest_file", &self.dest_file())
            .field("src_file", &self.src_file())
            .field("dst_offset", &self.dst_offset)
            .field("src_offset", &self.src_offset)
            .field("size", &self.size)
            .finish()
    }
}

type Pad = [u8; 124];

#[repr(C)]
union Body {
    allocate: Allocate,
    pointer: AddPointer,
    checksum: AddChecksum,
    wr_pointer: WritePointer,
    padding: Pad,
}

impl Default for Body {
    fn default() -> Self {
        Body {
            padding: [Default::default(); 124],
        }
    }
}

#[repr(C)]
#[derive(Default)]
struct RomfileCommand {
    tag: u32,
    body: Body,
}

#[derive(Debug)]
enum Command<'a> {
    Allocate(&'a Allocate),
    AddPointer(&'a AddPointer),
    AddChecksum(&'a AddChecksum),
    WritePointer(&'a WritePointer),
}

impl Command<'_> {
    pub fn invoke(&self, fwcfg: &mut FwCfg, acpi_digest: &mut Sha256) -> Result<(), &'static str> {
        match self {
            Command::Allocate(allocate) => allocate.invoke(fwcfg, acpi_digest),
            Command::AddPointer(add_pointer) => add_pointer.invoke(),
            Command::AddChecksum(add_checksum) => add_checksum.invoke(),
            Command::WritePointer(write_pointer) => write_pointer.invoke(),
        }
    }
}

impl RomfileCommand {
    fn tag(&self) -> Option<CommandTag> {
        CommandTag::from_repr(self.tag)
    }

    fn extract(&self) -> Result<Command<'_>, &'static str> {
        // Safety: we extract the value out of the union based on the tag value, which is safe to
        // do.
        match self.tag() {
            Some(CommandTag::Allocate) => Ok(Command::Allocate(unsafe { &self.body.allocate })),
            Some(CommandTag::AddPointer) => Ok(Command::AddPointer(unsafe { &self.body.pointer })),
            Some(CommandTag::AddChecksum) => {
                Ok(Command::AddChecksum(unsafe { &self.body.checksum }))
            }
            Some(CommandTag::WritePointer) => {
                Ok(Command::WritePointer(unsafe { &self.body.wr_pointer }))
            }
            _ => Err("Invalid command tag in table-loader"),
        }
    }

    fn invoke(&self, fwcfg: &mut FwCfg, acpi_digest: &mut Sha256) -> Result<(), &'static str> {
        if self.tag > 0x80000000 {
            log::warn!(
                "ignoring proprietary ACPI linker command with tag {:#x}",
                self.tag
            );
            return Ok(());
        }
        if self.tag == 0 {
            // Safety: interpreting the union as a byte array is safe, as it makes no assumptions
            // about the meaning of any of the bytes.
            log::debug!(
                "ignoring empty ACPI linker command with body {:?}",
                unsafe { &self.body.padding }
            );
            return Ok(());
        }
        self.extract()?.invoke(fwcfg, acpi_digest)
    }
}

/// Populates the ACPI tables per linking instructions in `etc/table-loader`.
///
/// Returns the address of the RSDP table.
pub fn build_acpi_tables(
    fwcfg: &mut FwCfg,
    acpi_digest: &mut Sha256,
) -> Result<&'static Rsdp, &'static str> {
    let file = fwcfg
        .find(TABLE_LOADER_FILE_NAME)
        .ok_or("Could not find 'etc/table-loader' in fw_cfg")?;

    if file.size() % core::mem::size_of::<RomfileCommand>() != 0 {
        return Err("length of 'etc/table-loader' is not a multiple of command struct size");
    }

    let buf = fwcfg.read_file_vec(&file)?;
    acpi_digest.update(&buf);

    // We can't use zerocopy::FromBytes/AsBytes here, as the fields of the structs have padding that
    // zerocopy doesn't support.
    // Safety: we're using `size_of` here to ensure that we don't go over the boundaries of the
    // original array.
    let commands = unsafe {
        core::slice::from_raw_parts(
            buf.as_ptr() as *const _ as *const RomfileCommand,
            buf.len() / core::mem::size_of::<RomfileCommand>(),
        )
    };

    for command in commands {
        command.invoke(fwcfg, acpi_digest)?;
    }

    // Safety: we ensure that the RSDP is valid before returning a reference to it.
    let rsdp = unsafe { RSDP.assume_init_ref() };
    rsdp.validate()?;
    Ok(rsdp)
}
