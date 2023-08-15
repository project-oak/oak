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

use crate::fw_cfg::FwCfg;
use core::{
    ffi::CStr,
    fmt::{Debug, Formatter, Result as FmtResult},
    mem::{size_of, zeroed, MaybeUninit},
    slice::from_raw_parts,
};
use strum::FromRepr;
use x86_64::VirtAddr;
use zerocopy::{AsBytes, FromBytes};

/// ACPI Root System Description Pointer.
///
/// Used to locate either the RSDT or XSDT in memory.
///
/// See Section 5.2.5 in the ACPI specification, Version 6.5 for more details.
#[derive(FromBytes, AsBytes)]
#[repr(C, packed)]
pub struct Rsdp {
    /// Signature: "RSD PTR " (note the trailing space).
    signature: [u8; 8],

    /// Checksum for fields defined in the ACPI 1.0 specification.
    checksum: u8,

    /// OEM-supplied identification string.
    oemid: [u8; 6],

    /// Revision of this structure.
    ///
    /// ACPI 1.0 value is zero, ACPI 2.0 value is 2.
    revision: u8,

    /// 32-bit physical address of the RSDT.
    rsdt_address: u32,

    // ACPI 2.0 fields.
    /// Length of the table, including the header.
    length: u32,

    /// 64-bit physical address of the XSDT.
    xsdt_address: u64,

    /// Checksum of the entire table, including both checksum fields.
    extended_checksum: u8,

    /// Reserved
    _reserved: [u8; 3],
}
static_assertions::assert_eq_size!(Rsdp, [u8; 36usize]);

impl Rsdp {
    fn validate(&self) -> Result<(), &'static str> {
        if &self.signature != b"RSD PTR " {
            return Err("Invalid RSDP signature");
        }
        let len = if self.revision > 2 { self.length } else { 20 } as usize;

        if len > size_of::<Rsdp>() {
            return Err("invalid RSDP size");
        }

        let checksum = self.as_bytes()[..20]
            .iter()
            .fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

        if checksum != 0 {
            return Err("Invalid RSDP checksum");
        }

        if self.revision > 2 {
            let checksum = self
                .as_bytes()
                .iter()
                .fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

            if checksum != 0 {
                return Err("Invalid RSDP extended checksum");
            }
        }

        // Check the pointer addresses; if they are valid, they should point within the EBDA.
        // Safety: we will never dereference the pointer, we just need to know where it points to.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        if self.rsdt_address > 0
            && ((self.rsdt_address as usize) < ebda_base
                || (self.rsdt_address as usize) >= ebda_base + EBDA_SIZE)
        {
            return Err("Invalid RSDT address: does not point to within EBDA");
        }
        if self.xsdt_address > 0
            && ((self.xsdt_address as usize) < ebda_base
                || (self.xsdt_address as usize) >= ebda_base + EBDA_SIZE)
        {
            return Err("Invalid XSDT address: does not point to within EBDA");
        }

        Ok(())
    }

    pub fn xsdt(&self) -> Result<Option<&Xsdt>, &'static str> {
        if self.xsdt_address == 0 {
            Ok(None)
        } else {
            Xsdt::new(VirtAddr::new(self.xsdt_address)).map(Some)
        }
    }
}

/// Header common for all ACPI tables.
///
/// See Section 5.2.6, System Description Table Header, in the ACPI specification for more details.
#[repr(C, packed)]
pub struct DescriptionHeader {
    /// ASCII string representation of the table identifer.
    pub signature: [u8; 4],

    /// Length of the table, in bytes, including the header.
    length: u32,

    /// Revision of the struture corresponding to the signature field for this table.
    revision: u8,

    /// The entire table, including the checksum field, must add to zero to be considered valid.
    checksum: u8,

    /// OEM-supplied string that identifies the OEM.
    oem_id: [u8; 6],

    /// OEM-supplied string that the OEM uses to identify the particular data table.
    oem_table_id: [u8; 8],

    /// OEM-supplied revision number.
    oem_revision: u32,

    /// Vendor ID of utility that created the table, e.g. the ASL Compiler.
    creator_id: u32,

    /// Revision of the utility that created the table, e.g. revision of the ASL Compiler.
    creator_revision: u32,
}

/// Extended System Description Table.
///
/// See Section 5.2.8 in the ACPI specification for more details.
#[repr(C, packed)]
pub struct Xsdt {
    header: DescriptionHeader,
    // The XSDT contains an array of pointers to other tables, but unfortunately this can't be
    // expressed in Rust.
}

impl Xsdt {
    pub fn new(addr: VirtAddr) -> Result<&'static Xsdt, &'static str> {
        // Safety: we're checking that the claimed XSDT is entirely within the EBDA.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        let xsdt = unsafe { &*addr.as_ptr::<Xsdt>() };

        if (addr.as_u64() as usize) < ebda_base
            || addr.as_u64() as usize + xsdt.header.length as usize > ebda_base + EBDA_SIZE
        {
            return Err("XSDT doesn't fit in EBDA");
        }
        xsdt.validate()?;
        Ok(xsdt)
    }

    fn validate(&self) -> Result<(), &'static str> {
        // Unfortunately we have to exceed our bounds to compute the checksum.
        // Safety: we've checked that the address + len is weithin the EBDA bounds in `new()`.
        let data =
            unsafe { from_raw_parts(self as *const _ as *const u8, self.header.length as usize) };
        let checksum = data.iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));
        if checksum != 0 {
            return Err("XSDT checksum invalid");
        }
        // Check that all the pointers within the XSDT point to locations within the EBDA.
        if (self.header.length as usize - size_of::<DescriptionHeader>()) % size_of::<usize>() != 0
        {
            return Err("XSDT invalid: entries size not a multiple of pointer size");
        }

        // Safety: we're never dereferencing the pointer.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        for &entry in self.entries() {
            let ptr = entry as *const _ as usize;
            if !(ebda_base..ebda_base + EBDA_SIZE).contains(&ptr) {
                return Err("XSDT invalid: entry points outside EBDA");
            }
        }
        Ok(())
    }

    pub fn entries(&self) -> &[&'static DescriptionHeader] {
        let entries_base = self as *const _ as usize + size_of::<DescriptionHeader>();
        // Safety: we've validated that the address and length makes sense in `validate()`.
        unsafe {
            from_raw_parts(
                entries_base as *const &DescriptionHeader,
                (self.header.length as usize - size_of::<DescriptionHeader>()) / size_of::<usize>(),
            )
        }
    }

    /// Finds a table based on the signature, if it is present.
    pub fn get(&self, table: &[u8; 4]) -> Option<&'static DescriptionHeader> {
        self.entries()
            .iter()
            .find(|&&entry| entry.signature == *table)
            .copied()
    }
}

// RSDP has to be within the first 1 KiB of EBDA, so we treat it separately. The full size of EBDA
// is 128 KiB, but let's reserve the whole 1 KiB for the RSDP.
const EBDA_SIZE: usize = 127 * 1024;
#[link_section = ".ebda.rsdp"]
static mut RSDP: MaybeUninit<Rsdp> = MaybeUninit::uninit();
#[link_section = ".ebda"]
static mut EBDA: MaybeUninit<[u8; EBDA_SIZE]> = MaybeUninit::uninit();

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

    fn invoke(&self, fwcfg: &mut FwCfg) -> Result<(), &'static str> {
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

            fwcfg.read_file(&file, buf.as_bytes_mut()).map(|_| ())
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
            fwcfg.read_file(&file, buf).map(|_| ())
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
    pub fn invoke(&self, fwcfg: &mut FwCfg) -> Result<(), &'static str> {
        match self {
            Command::Allocate(allocate) => allocate.invoke(fwcfg),
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

    fn invoke(&self, fwcfg: &mut FwCfg) -> Result<(), &'static str> {
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
        self.extract()?.invoke(fwcfg)
    }
}

/// Populates the ACPI tables per linking instructions in `etc/table-loader`.
///
/// Returns the address of the RSDP table.
pub fn build_acpi_tables(fwcfg: &mut FwCfg) -> Result<&'static Rsdp, &'static str> {
    let mut commands: [RomfileCommand; 32] = Default::default();

    let file = fwcfg
        .find(TABLE_LOADER_FILE_NAME)
        .ok_or("Could not find 'etc/table-loader' in fw_cfg")?;

    if file.size() % core::mem::size_of::<RomfileCommand>() != 0 {
        return Err("length of 'etc/table-loader' is not a multiple of command struct size");
    }

    if file.size() > core::mem::size_of_val(&commands) {
        return Err("too many commands in 'etc/table-loader'");
    }

    // We can't use zerocopy::FromBytes/AsBytes here, as the fields of the structs have padding that
    // zerocopy doesn't support.
    // Safety: we're using `size_of` here to ensure that we don't go over the boundaries of the
    // original array.

    fwcfg.read_file(&file, unsafe {
        core::slice::from_raw_parts_mut(
            &mut commands as *mut _ as usize as *mut u8,
            core::mem::size_of_val(&commands),
        )
    })?;

    for command in &commands[..(file.size() / core::mem::size_of::<RomfileCommand>())] {
        command.invoke(fwcfg)?;
    }

    // Safety: we ensure that the RSDP is valid before returning a reference to it.
    let rsdp = unsafe { RSDP.assume_init_ref() };
    rsdp.validate()?;
    Ok(rsdp)
}
