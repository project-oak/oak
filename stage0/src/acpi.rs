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

//! This module provides functions to build ACPI tables content from commands
//! received from the VMM.

// These data structures (and constants) are derived from
// qemu/hw/acpi/bios-linker-loader.c that defines the interface.
use alloc::{boxed::Box, collections::btree_map::BTreeMap};
use core::{
    alloc::{Allocator, Layout},
    ffi::CStr,
    fmt::{Debug, Formatter, Result as FmtResult},
    mem::size_of_val,
    ops::Deref,
    pin::Pin,
};

use sha2::{Digest, Sha256};
use spinning_top::Spinlock;
use strum::FromRepr;
use zerocopy::AsBytes;

use crate::{
    acpi_tables::{
        DescriptionHeader, MultiprocessorWakeup, ProcessorLocalApic, ProcessorLocalX2Apic, Rsdp,
    },
    allocator::BumpAllocator,
    fw_cfg::FwCfg,
    Madt,
};

pub struct Ebda<'a, A: Allocator> {
    alloc: &'a A,
    files: BTreeMap<RomfileName, Box<[u8], &'a A>>,
}

impl<'a: 'static, A: Allocator> Ebda<'a, A> {
    const fn new(alloc: &'a A) -> Self {
        Ebda { alloc, files: BTreeMap::new() }
    }

    /// Creates a new file in memory provided by the EBDA allocator.
    ///
    /// Returns an error if a file with such a name already exists or memory
    /// could not be allocated.
    pub fn new_file(
        &mut self,
        name: &RomfileName,
        size: usize,
        align: usize,
    ) -> Result<&mut [u8], &'static str> {
        if self.files.contains_key(name) {
            return Err("duplicate file in table_loader");
        }

        // Unfortunately the memory allocation is fairly convoluted because two
        // requirements:
        // 1. We need to guaratnee alignment to `align`, but `u8` doesn't care about
        //    alignment. Therefore we can't just use `Box::new_zeroed_slice_in`.
        // 2. We need to allocate memory from `EBDA_ALLOCATOR`.
        // Note that boxing the value is mostly for good Rust hygiene, as
        // the map itself that will own the files will be 'static, and
        // `BumpAllocator` doesn't support deallocation anyway. But it makes testing
        // easier.

        // Step 1: allocate a pile of raw memory.
        let mem = self
            .alloc
            .allocate_zeroed(
                Layout::from_size_align(size, align)
                    .map_err(|_| "invalid alignment in file_loader")?,
            )
            .map_err(|_| "memory allocation failure in file_loader")?;

        // Step 2: wrap it in a `Box` so that we wouldn't leak memory.
        // Ideally we'd call `Box::from_non_null_in`, but our current version of Rust
        // doesn't have that.
        // Safety: we only call the method once (so no double-free can occur); we've
        // allocated the memory from the specified allocator; and any layout (and
        // content) is valid for [u8].
        let mem = unsafe { Box::from_raw_in(mem.as_ptr(), self.alloc) };

        self.files.insert(*name, mem);
        self.get_file_mut(name)
    }

    pub fn get_file(&self, name: &RomfileName) -> Result<&[u8], &'static str> {
        self.files.get(name).map(|v| &**v).ok_or("file not found in table_loader")
    }

    pub fn get_file_mut(&mut self, name: &RomfileName) -> Result<&mut [u8], &'static str> {
        self.files.get_mut(name).map(|x| x.as_mut()).ok_or("file not found in table_loader")
    }

    pub fn get_rsdp_mut(&mut self) -> Result<Pin<&'a mut Rsdp>, &'static str> {
        for (name, value) in self.files.iter_mut() {
            if CStr::from_bytes_until_nul(name)
                .map_err(|_| "invalid table_loader file name")?
                .to_bytes()
                .ends_with(RSDP_FILE_NAME_SUFFIX.as_bytes())
            {
                let mem = value.as_mut_ptr();

                // Safety: we will validate the RSDP before returning the value.
                let rsdp: &mut Rsdp = unsafe { &mut *(mem as *mut Rsdp) };
                rsdp.validate()?;
                // We need to ensure the `Rsdp` doesn't move in memory, so it gets `Pin`-ned.
                return Ok(Pin::new(rsdp));
            }
        }

        Err("RSDP not found in loaded ACPI tables")
    }
}

pub const EBDA_SIZE: usize = 127 * 1024;
type EbdaAllocator = BumpAllocator<EBDA_SIZE>;

/// EBDA memory: 128K of memory just below 0xA_0000 (enforced in the linker
/// script).
#[link_section = ".ebda"]
pub static EBDA_ALLOCATOR: EbdaAllocator = EbdaAllocator::uninit();

/// Wrapper around the EBDA allocator that manages file_loader files in the EBDA
/// memory.
pub static EBDA: Spinlock<Ebda<EbdaAllocator>> = Spinlock::new(Ebda::new(&EBDA_ALLOCATOR));

const TABLE_LOADER_FILE_NAME: &CStr =
    unsafe { CStr::from_bytes_with_nul_unchecked(b"etc/table-loader\0") };
const RSDP_FILE_NAME_SUFFIX: &str = "acpi/rsdp";

const ROMFILE_LOADER_FILESZ: usize = 56;

type RomfileName = [u8; ROMFILE_LOADER_FILESZ];

#[repr(u32)]
#[derive(Debug, Eq, FromRepr, Ord, PartialEq, PartialOrd)]
enum CommandTag {
    Allocate = 1,
    AddPointer = 2,
    AddChecksum = 3,
    WritePointer = 4,

    // Extended VMM-specific commands
    AddPciHoles = 0x80000001,
}

impl CommandTag {
    /// VMM-specific commands that are not supported by QEMU should have the
    /// highest bit set.
    const VMM_SPECIFIC: u32 = 0x80000000;
}

#[repr(u8)]
#[derive(Debug, FromRepr)]
enum Zone {
    High = 1,
    FSeg = 2,
}

/// COMMAND_ALLOCATE - allocate a table from `file` subject to `align` alignment
/// (must be power of
/// 2) and `zone` (can be HIGH or FSEG) requirements.
///
/// Must appear exactly once for each file, and before this file is referenced
/// by any other command.
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

    fn invoke<P: crate::Platform>(
        &self,
        fwcfg: &mut FwCfg<P>,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        let file = fwcfg.find(self.file()).unwrap();

        let mut ebda = EBDA.lock();
        let buf = ebda.new_file(&self.file, file.size(), self.align as usize)?;

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

/// COMMAND_ADD_POINTER - patch the table (originating from `dest_file`) at
/// `offset`, by adding a pointer to the table originating from `src_file`.
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
        let mut ebda = EBDA.lock();

        let src_file_ptr = ebda.get_file(&self.src_file)?.as_ptr();
        let dest_file = ebda.get_file_mut(&self.dest_file)?;

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

/// COMMAND_ADD_CHECKSUM - calculate checksum of the range specified by `start`
/// and `length` fields, and then add the value at `offset`.
///
/// Checksum simply sums -X for each byte X in the range using 8-bit math (or in
/// our case, we just sum together all the numbers and subtract in the end.)
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
        let mut ebda = EBDA.lock();
        let file = ebda.get_file_mut(&self.file)?;

        if self.start as usize > file.len()
            || (self.start + self.length) as usize > file.len()
            || self.offset as usize > file.len()
        {
            return Err("COMMAND_ADD_CHECKSUM invalid; read or write would overflow file");
        }

        let checksum =
            AddChecksum::checksum(&file[self.start as usize..(self.start + self.length) as usize]);
        let val = file.get_mut(self.offset as usize).unwrap();
        *val = val.wrapping_sub(checksum);
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

/// COMMAND_WRITE_POINTER - write the fw_cfg file (originating from `dest_file`)
/// at `offset`, by adding a pointer to `src_offset` within the table
/// originating from `src_file`.
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

#[repr(C)]
#[derive(Copy, Clone)]
struct AddPciHoles {
    file: RomfileName,
    pci_start_offset_32: u32,
    pci_end_offset_32: u32,
    pci_valid_offset_64: u32,
    pci_start_offset_64: u32,
    pci_end_offset_64: u32,
    pci_length_offset_64: u32,
    _padding: [u8; 42],
}
static_assertions::assert_eq_size!(AddPciHoles, Pad);

struct Window<T> {
    base: T,
    end: T,
}

impl<T: core::ops::Sub<Output = T> + Copy> Window<T> {
    fn len(&self) -> T {
        self.end - self.base
    }
}

struct FirmwareData {
    pci_window_32: Window<u32>,
    pci_window_64: Window<u64>,
}

fn populate_firmware_data() -> Result<FirmwareData, &'static str> {
    // There may be a way how to dynamically determine these values, but for now,
    // hard-code the expected values as it's unlikely they will ever change.

    Ok(FirmwareData {
        pci_window_32: Window { base: 0xE0000000u32, end: 0xFEBFF000u32 },
        pci_window_64: Window { base: 0x8000000000u64, end: 0x10000000000u64 },
    })
}

impl AddPciHoles {
    pub fn file(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.file).unwrap()
    }

    fn invoke(&self) -> Result<(), &'static str> {
        let mut ebda = EBDA.lock();
        let file = ebda.get_file_mut(&self.file)?;

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

        let data: FirmwareData = populate_firmware_data()?;

        // 32 bit
        file[self.pci_start_offset_32 as usize
            ..(self.pci_start_offset_32 as usize + size_of_val(&data.pci_window_32.base))]
            .copy_from_slice(&data.pci_window_32.base.to_le_bytes());
        file[self.pci_end_offset_32 as usize
            ..(self.pci_end_offset_32 as usize + size_of_val(&data.pci_window_32.end))]
            .copy_from_slice(&data.pci_window_32.end.to_le_bytes());

        // 64-bit
        if data.pci_window_64.base != 0 {
            file[self.pci_valid_offset_64 as usize] = 1;
            file[self.pci_start_offset_64 as usize
                ..(self.pci_start_offset_64 as usize + size_of_val(&data.pci_window_64.base))]
                .copy_from_slice(&data.pci_window_64.base.to_le_bytes());
            file[self.pci_end_offset_64 as usize
                ..(self.pci_end_offset_64 as usize + size_of_val(&data.pci_window_64.end))]
                .copy_from_slice(&data.pci_window_64.end.to_le_bytes());
            file[self.pci_length_offset_64 as usize
                ..(self.pci_length_offset_64 as usize + size_of_val(&data.pci_window_64.len()))]
                .copy_from_slice(&data.pci_window_64.len().to_le_bytes());
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

type Pad = [u8; 124];

#[repr(C)]
union Body {
    allocate: Allocate,
    pointer: AddPointer,
    checksum: AddChecksum,
    wr_pointer: WritePointer,
    pci_holes: AddPciHoles,
    padding: Pad,
}

impl Default for Body {
    fn default() -> Self {
        Body { padding: [Default::default(); 124] }
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
    AddPciHoles(&'a AddPciHoles),
}

impl Command<'_> {
    pub fn invoke<P: crate::Platform>(
        &self,
        fwcfg: &mut FwCfg<P>,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        match self {
            Command::Allocate(allocate) => allocate.invoke(fwcfg, acpi_digest),
            Command::AddPointer(add_pointer) => add_pointer.invoke(),
            Command::AddChecksum(add_checksum) => add_checksum.invoke(),
            Command::WritePointer(write_pointer) => write_pointer.invoke(),
            Command::AddPciHoles(add_pci_holes) => add_pci_holes.invoke(),
        }
    }
}

impl RomfileCommand {
    fn tag(&self) -> Option<CommandTag> {
        CommandTag::from_repr(self.tag)
    }

    fn extract(&self) -> Result<Command<'_>, &'static str> {
        // Safety: we extract the value out of the union based on the tag value, which
        // is safe to do.
        match self.tag() {
            Some(CommandTag::Allocate) => Ok(Command::Allocate(unsafe { &self.body.allocate })),
            Some(CommandTag::AddPointer) => Ok(Command::AddPointer(unsafe { &self.body.pointer })),
            Some(CommandTag::AddChecksum) => {
                Ok(Command::AddChecksum(unsafe { &self.body.checksum }))
            }
            Some(CommandTag::WritePointer) => {
                Ok(Command::WritePointer(unsafe { &self.body.wr_pointer }))
            }
            Some(CommandTag::AddPciHoles) => {
                Ok(Command::AddPciHoles(unsafe { &self.body.pci_holes }))
            }
            _ => Err("Invalid command tag in table-loader"),
        }
    }

    fn invoke<P: crate::Platform>(
        &self,
        fwcfg: &mut FwCfg<P>,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        if self.tag > CommandTag::VMM_SPECIFIC && self.tag().is_none() {
            log::warn!("ignoring proprietary ACPI linker command with tag {:#x}", self.tag);
            return Ok(());
        }
        if self.tag == 0 {
            // Safety: interpreting the union as a byte array is safe, as it makes no
            // assumptions about the meaning of any of the bytes.
            log::debug!("ignoring empty ACPI linker command with body {:?}", unsafe {
                &self.body.padding
            });
            return Ok(());
        }
        self.extract()?.invoke(fwcfg, acpi_digest)
    }
}

/// Populates the ACPI tables per linking instructions in `etc/table-loader`.
///
/// Returns the address of the RSDP table.
pub fn build_acpi_tables<P: crate::Platform>(
    fwcfg: &mut FwCfg<P>,
    acpi_digest: &mut Sha256,
) -> Result<&'static Rsdp, &'static str> {
    let file =
        fwcfg.find(TABLE_LOADER_FILE_NAME).ok_or("Could not find 'etc/table-loader' in fw_cfg")?;

    if file.size() % core::mem::size_of::<RomfileCommand>() != 0 {
        return Err("length of 'etc/table-loader' is not a multiple of command struct size");
    }

    let buf = fwcfg.read_file_vec(&file)?;
    acpi_digest.update(&buf);

    // We can't use zerocopy::FromBytes/AsBytes here, as the fields of the structs
    // have padding that zerocopy doesn't support.
    // Safety: we're using `size_of` here to ensure that we don't go over the
    // boundaries of the original array.
    let commands = unsafe {
        core::slice::from_raw_parts(
            buf.as_ptr() as *const _ as *const RomfileCommand,
            buf.len() / core::mem::size_of::<RomfileCommand>(),
        )
    };

    for command in commands {
        command.invoke(fwcfg, acpi_digest)?;
    }

    let mut rsdp = EBDA.lock().get_rsdp_mut()?;
    log::info!("ACPI tables before finalizing:");
    debug_print_acpi_tables(&rsdp)?;

    log::info!("Finalizing RSDP");
    P::finalize_acpi_tables(rsdp.as_mut().get_mut())?;
    rsdp.validate()?;
    log::info!("ACPI tables after finalizing:");
    debug_print_acpi_tables(&rsdp)?;

    Ok(rsdp.into_ref().get_ref())
}

/// Prints ACPI metadata including RSDP, RSDT and XSDT (if present).
fn debug_print_acpi_tables(rsdp: &Rsdp) -> Result<(), &'static str> {
    log::info!("RSDP location: {:#018x}", rsdp as *const _ as u64);
    log::info!("RSDP: {:?}", rsdp);

    if let Some(rsdt) = rsdp.rsdt() {
        let rsdt = rsdt?;
        log::info!("RSDT: {:?}", rsdt);
        log::info!("RSDT entry count: {}", rsdt.entry_headers().count());
        print_system_data_table_entries(rsdt.entry_headers())?;
    } else {
        log::info!("No RSDT present");
    }

    if let Some(xsdt) = rsdp.xsdt() {
        let xsdt = xsdt?;
        log::info!(
            "XSDT ({:#x}-{:#x}): {:?}",
            xsdt.addr_range().start,
            xsdt.addr_range().end,
            xsdt
        );
        log::info!("XSDT entry count: {}", xsdt.entry_ptrs().count());
        print_system_data_table_entries(
            xsdt.entry_ptrs()
                .map(|entry_ptr_or_err| entry_ptr_or_err.map(|entry_ptr| entry_ptr.deref())),
        )?;
    } else {
        log::info!("No XSDT present");
    }
    Ok(())
}

/// Prints RSDT or XSDT entries. Prints extra detail for MADT entry.
fn print_system_data_table_entries<'a>(
    entries: impl Iterator<Item = Result<&'a DescriptionHeader, &'static str>>,
) -> Result<(), &'static str> {
    for header in entries {
        let header = header?;
        log::info!("{}", header);
        if header.signature == *Madt::SIGNATURE {
            log::info!("    Entry APIC - It is a MADT, Interrupt Controller Structures:");
            let madt = Madt::new(header)?;
            for madt_entry in madt.controller_struct_headers() {
                match madt_entry.structure_type {
                    ProcessorLocalApic::STRUCTURE_TYPE => {
                        log::info!("    -> Local APIC: {:?}", ProcessorLocalApic::new(madt_entry)?);
                    }
                    ProcessorLocalX2Apic::STRUCTURE_TYPE => {
                        log::info!(
                            "    -> Local X2APIC: {:?}",
                            ProcessorLocalX2Apic::new(madt_entry)?
                        );
                    }
                    MultiprocessorWakeup::STRUCTURE_TYPE => {
                        log::info!(
                            "    -> MultiprocessorWakeup: {:?}",
                            MultiprocessorWakeup::from_header_cast(madt_entry)?
                        );
                    }
                    _ => {
                        log::info!(
                            "    -> Unknown structure, type = {}",
                            madt_entry.structure_type
                        );
                    }
                }
            }
        }
    }
    Ok(())
}
