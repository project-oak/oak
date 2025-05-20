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
use core::{
    alloc::Layout,
    cell::OnceCell,
    ffi::CStr,
    fmt::{Debug, Formatter, Result as FmtResult},
    mem::{size_of, size_of_val, zeroed, MaybeUninit},
    ops::{Deref, DerefMut, Range},
};

use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use sha2::{Digest, Sha256};
use strum::FromRepr;
use zerocopy::AsBytes;

use crate::{
    acpi_tables::{
        DescriptionHeader, MultiprocessorWakeup, ProcessorLocalApic, ProcessorLocalX2Apic, Rsdp,
    },
    fw_cfg::{DirEntry, FwCfg},
    Madt, ZeroPage,
};

/// Root System Descriptor Pointer.
/// Not really a pointer but a structure (see https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html#root-system-description-pointer-rsdp).#
/// It's located in the first 1KiB of the EBDA.
#[link_section = ".ebda"]
static mut EBDA: MaybeUninit<Rsdp> = MaybeUninit::uninit();

/// How much memory to reserve for ACPI tables in "high" memory.
const HIGH_MEM_SIZE: usize = 0x10_0000;

// Raw chunk of the "high" memory for ACPI tables. This should get replaced by a
// proper allocator as part of clean-up.
static mut HIGH_MEM: OnceCell<&'static mut [u8]> = OnceCell::new();

static mut HIGH_MEM_ALLOC: OnceCell<Ebda> = OnceCell::new();

const TABLE_LOADER_FILE_NAME: &CStr = c"etc/table-loader";
const RSDP_FILE_NAME_SUFFIX: &str = "acpi/rsdp";
const ACPI_TABLES_FILE_NAME_SUFFIX: &str = "acpi/tables";

const ROMFILE_LOADER_FILESZ: usize = 56;

type RomfileName = [u8; ROMFILE_LOADER_FILESZ];

/// A really simple virtual file system interface to store chunks of bytes by
/// name, and access said chunks later by the name.
trait Files {
    /// Allocate a new file.
    ///
    /// This is similar to the normal `Allocator` API, but we may need to treat
    /// files in different `zone`-s differently (e.g. allocate from different
    /// pools of memory), so we can't just piggyback on the `Allocator` trait
    /// directly.
    ///
    /// Alignment guarantees requested the layout are implementation-specific
    /// (for example, if you use a non-static buffer of u8-s as the backing
    /// store, we can't guarantee alignment as the data can be moved around
    /// freely after allocation.)
    ///
    /// Returns an error if the file already exists.
    fn allocate(
        &mut self,
        name: &CStr,
        layout: Layout,
        zone: Zone,
    ) -> Result<&mut [u8], &'static str>;

    /// Get a mutable reference to file contents, if such file exists.
    fn get_file_mut(&mut self, name: &CStr) -> Result<&mut [u8], &'static str>;

    /// Access the contents of the named file, if it exists.
    fn get_file(&self, name: &CStr) -> Result<&[u8], &'static str>;
}

/// Implementation for `Files` that just delegates to the existing EBDA space.
struct EbdaFiles;

impl Files for EbdaFiles {
    fn allocate(
        &mut self,
        name: &CStr,
        layout: Layout,
        _zone: Zone,
    ) -> Result<&mut [u8], &'static str> {
        let name = name.to_str().map_err(|_| "invalid file name")?;

        if name.ends_with(RSDP_FILE_NAME_SUFFIX) {
            // ACPI 1.0 RSDP is 20 bytes, ACPI 2.0 RSDP is 36 bytes.
            // We don't really care which version we're dealing with, as long as the data
            // structure is one of the two.
            if layout.size() > size_of::<Rsdp>() || (layout.size() != 20 && layout.size() != 36) {
                return Err("RSDP doesn't match expected size");
            }

            // Safety: we do not have concurrent threads so accessing the static is safe.
            let buf = unsafe { EBDA.write(zeroed()) };

            // Sanity checks.
            if (buf as *const _ as u64) < 0x80000 || (buf as *const _ as u64) > 0x81000 {
                log::error!("RSDP address: {:p}", buf);
                return Err("RSDP address is not within the first 1 KiB of EBDA");
            }
            if (buf as *const _ as u64) % layout.align() as u64 != 0 {
                return Err("RSDP address not aligned properly");
            }
            Ok(buf.as_bytes_mut())
        } else if name.ends_with(ACPI_TABLES_FILE_NAME_SUFFIX) {
            let ebda = Ebda::instance();
            ebda.check_alignment(layout.align() as u32)?;
            ebda.allocate(layout.size())
        } else {
            Err("Unsupported file in table-loader")
        }
    }

    fn get_file_mut(&mut self, name: &CStr) -> Result<&mut [u8], &'static str> {
        // TODO: b/380246359 - When Ebda wraps around Rsdp too, remove these
        // direct accesses to EBDA_MEM to guarantee Ebda::len stays correct.

        // Safety: we do not have concurrent threads so accessing the static is safe,
        // and even if Allocate has not been called yet, all values are valid for an
        // [u8].
        let name = name.to_str().map_err(|_| "invalid file name")?;
        if name.ends_with(RSDP_FILE_NAME_SUFFIX) {
            Ok(unsafe { EBDA.assume_init_mut().as_bytes_mut() })
        } else if name.ends_with(ACPI_TABLES_FILE_NAME_SUFFIX) {
            unsafe { HIGH_MEM.get_mut() }
                .map(DerefMut::deref_mut)
                .ok_or("high memory for ACPI not initialized yet")
        } else {
            Err("Unsupported file in table-loader")
        }
    }

    fn get_file(&self, name: &CStr) -> Result<&[u8], &'static str> {
        // TODO: b/380246359 - When Ebda wraps around Rsdp too, remove these
        // direct accesses to EBDA_MEM to guarantee Ebda::len stays correct.

        // Safety: we do not have concurrent threads so accessing the static is safe,
        // and even if Allocate has not been called yet, all values are valid for an
        // [u8].
        let name = name.to_str().map_err(|_| "invalid file name")?;
        if name.ends_with(RSDP_FILE_NAME_SUFFIX) {
            Ok(unsafe { EBDA.assume_init_ref().as_bytes() })
        } else if name.ends_with(ACPI_TABLES_FILE_NAME_SUFFIX) {
            unsafe { HIGH_MEM.get() }
                .map(Deref::deref)
                .ok_or("high memory for ACPI not initialized yet")
        } else {
            Err("Unsupported file in table-loader")
        }
    }
}

/// Interface for firmware functions that we need: namely, how to load the
/// configuration files.
///
/// This is effectively a subset of the `FwCfg` API that we need for building
/// tables.
trait Firmware {
    fn find(&mut self, name: &CStr) -> Option<DirEntry>;
    fn read_file(&mut self, file: &DirEntry, buf: &mut [u8]) -> Result<usize, &'static str>;
}

/// `FwCfg` is pretty much the canonical implementation of `Firmware` for our
/// use cases.
impl<P: crate::Platform> Firmware for FwCfg<P> {
    fn find(&mut self, name: &CStr) -> Option<DirEntry> {
        self.find(name)
    }

    fn read_file(&mut self, file: &DirEntry, buf: &mut [u8]) -> Result<usize, &'static str> {
        self.read_file(file, buf)
    }
}

/// A wrapper around EBDA memory with helpers to manage it.
// TODO: b/380246359 - let Ebda wrap around both RSDP and the rest of EBDA.
#[derive(Debug)]
pub struct Ebda {
    ebda_buf: &'static mut [u8],
    /// Count of bytes actually used within ebda_buf.
    len_bytes: usize,
}

impl Ebda {
    pub fn instance() -> &'static mut Ebda {
        // Safety: EBDA_INSTANCE accessed for write only from a single thread (BSP).
        // Read-only access from APs (assembly code).
        unsafe {
            match HIGH_MEM_ALLOC.get_mut() {
                Some(ebda) => ebda,
                None => {
                    // Safety: Either the cell is initalized or we panic.
                    let ebda = Self {
                        ebda_buf: HIGH_MEM
                            .get_mut()
                            .expect("high memory for ACPI not initialized yet"),

                        len_bytes: 0,
                    };
                    HIGH_MEM_ALLOC.set(ebda).unwrap();
                    HIGH_MEM_ALLOC.get_mut().unwrap()
                }
            }
        }
    }

    /// Allocates byte_count of memory on the EBDA and returns a slice to it.
    pub fn allocate(&mut self, byte_count: usize) -> Result<&mut [u8], &'static str> {
        let dest_base_ix = self.len_bytes;
        let dest_top_ix = dest_base_ix + byte_count;

        self.len_bytes += byte_count;
        Ok(self.ebda_buf[dest_base_ix..dest_top_ix].as_mut())
    }

    pub fn check_alignment(&self, required_alignment: u32) -> Result<(), &'static str> {
        let start = self.ebda_buf.as_ptr_range().start as u64;
        if start % required_alignment as u64 != 0 {
            log::error!(
                "ACPI tables address: {:#018x}, required alignment: {}",
                start,
                required_alignment
            );
            return Err("ACPI tables address not aligned properly");
        }
        Ok(())
    }

    /// Returns true if addr is within EBDA address range.
    /// Convenience method for validations.
    pub fn contains_addr(&self, addr: usize) -> bool {
        self.ebda_buf.as_ptr_range().contains(&(addr as *const u8))
    }

    pub fn contains_addr_range(&self, range: &Range<usize>) -> bool {
        self.contains_addr(range.start) && self.contains_addr(range.end)
    }
}

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

trait Invoke<FW: Firmware, F: Files> {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str>;
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
    #[cfg(test)]
    pub fn new<T: AsBytes + ?Sized>(file: &T, align: u32, zone: Zone) -> Self {
        let mut cmd =
            Self { file: [0; ROMFILE_LOADER_FILESZ], align, zone: zone as u8, _padding: [0; 60] };
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
        acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
        let file = fwcfg.find(self.file()).unwrap();

        let layout = Layout::from_size_align(file.size(), self.align as usize)
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
    #[cfg(test)]
    pub fn new<T: AsBytes + ?Sized>(dest_file: &T, src_file: &T, offset: u32, size: u8) -> Self {
        let mut cmd = Self {
            dest_file: [0; ROMFILE_LOADER_FILESZ],
            src_file: [0; ROMFILE_LOADER_FILESZ],
            offset,
            size,
            _padding: [0; 6],
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
///
/// See `bios_linker_loader_add_checksum()` in QEMU
/// `hw/acpi/bios-linker-loader.c` for the best available documentation.
#[repr(C)]
#[derive(Copy, Clone)]
struct AddChecksum {
    file: RomfileName,
    /// Location of the checksum to be patched within the file, relative to the
    /// start of the file
    offset: u32,

    /// Start of the data in the file to checksum, relative to the start of the
    /// file
    start: u32,

    /// Size of the data in the file to checksum, offset from `start`
    length: u32,
    _padding: [u8; 54],
}
static_assertions::assert_eq_size!(AddChecksum, Pad);

impl AddChecksum {
    #[cfg(test)]
    pub fn new<T: AsBytes + ?Sized>(file: &T, offset: u32, start: u32, length: u32) -> Self {
        let mut cmd =
            Self { file: [0; ROMFILE_LOADER_FILESZ], offset, start, length, _padding: [0; 54] };
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
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for WritePointer {
    fn invoke(
        &self,
        _files: &mut F,
        _fwcfg: &mut FW,
        _acpi_digest: &mut Sha256,
    ) -> Result<(), &'static str> {
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
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for AddPciHoles {
    fn invoke(
        &self,
        files: &mut F,
        _fwcfg: &mut FW,
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

impl PartialEq for Body {
    fn eq(&self, other: &Self) -> bool {
        // Compare raw bytes.
        // Safety: every byte sequence is valid as a u8 array.
        unsafe { self.padding == other.padding }
    }
}

#[repr(C)]
#[derive(Default, PartialEq)]
struct RomfileCommand {
    tag: u32,
    body: Body,
}

impl From<Allocate> for RomfileCommand {
    fn from(allocate: Allocate) -> Self {
        RomfileCommand { tag: CommandTag::Allocate as u32, body: Body { allocate } }
    }
}

impl From<AddPointer> for RomfileCommand {
    fn from(pointer: AddPointer) -> Self {
        RomfileCommand { tag: CommandTag::AddPointer as u32, body: Body { pointer } }
    }
}

impl From<AddChecksum> for RomfileCommand {
    fn from(checksum: AddChecksum) -> Self {
        RomfileCommand { tag: CommandTag::AddChecksum as u32, body: Body { checksum } }
    }
}

impl Debug for RomfileCommand {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // Safety: we check the tags; if a tag is not recognized, you get the padding
        // which accepts all values.
        f.debug_struct("RomfileCommand")
            .field("tag", &self.tag)
            .field(
                "body",
                match self.tag() {
                    Some(CommandTag::Allocate) => unsafe { &self.body.allocate },
                    Some(CommandTag::AddPointer) => unsafe { &self.body.pointer },
                    Some(CommandTag::AddChecksum) => unsafe { &self.body.checksum },
                    Some(CommandTag::WritePointer) => unsafe { &self.body.wr_pointer },
                    Some(CommandTag::AddPciHoles) => unsafe { &self.body.pci_holes },
                    _ => unsafe { &self.body.padding },
                },
            )
            .finish()
    }
}

impl RomfileCommand {
    fn tag(&self) -> Option<CommandTag> {
        CommandTag::from_repr(self.tag)
    }
}

impl<FW: Firmware, F: Files> Invoke<FW, F> for RomfileCommand {
    fn invoke(
        &self,
        files: &mut F,
        fwcfg: &mut FW,
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

        // Safety: we extract the value out of the union based on the tag value, which
        // is safe to do.
        let command: &dyn Invoke<FW, F> = match self.tag() {
            Some(CommandTag::Allocate) => unsafe { &self.body.allocate },
            Some(CommandTag::AddPointer) => unsafe { &self.body.pointer },
            Some(CommandTag::AddChecksum) => unsafe { &self.body.checksum },
            Some(CommandTag::WritePointer) => unsafe { &self.body.wr_pointer },
            Some(CommandTag::AddPciHoles) => unsafe { &self.body.pci_holes },
            _ => return Err("Invalid command tag in table-loader"),
        };
        command.invoke(files, fwcfg, acpi_digest)
    }
}

pub fn setup_high_allocator(zero_page: &mut ZeroPage) -> Result<(), &'static str> {
    let mem_start = {
        // Find a suitable 1M gap: we want it to be as close to the 1G mark as possible,
        // but we may have less memory than that.
        let entry = zero_page
            .e820_table()
            .iter()
            .filter(|&entry| {
                // We're only interested in (a) entries that are regular memory and (b) that
                // start below the 1G mark, with enough space for a 1M chunk.
                entry.entry_type() == Some(E820EntryType::RAM)
                    && entry.addr() < (0x4000_0000 - HIGH_MEM_SIZE)
                    && entry.size() >= HIGH_MEM_SIZE
            })
            .last()
            .ok_or("could not find memory for ACPI tables")?;
        let mem_end = core::cmp::min(0x4000_0000, entry.addr() + entry.size());
        mem_end - HIGH_MEM_SIZE
    };
    // reserve the memory for ACPI tables
    zero_page.insert_e820_entry(BootE820Entry::new(mem_start, HIGH_MEM_SIZE, E820EntryType::ACPI));

    // Safety: the pointer should only be written once, and we're single threaded,
    // and if it is nullptr any allocations would have panicked by now.
    // TODO: b/409562112 - This should be replaced by a proper allocator instead of
    // juggling raw pointers.
    unsafe { HIGH_MEM.set(core::slice::from_raw_parts_mut(mem_start as *mut u8, HIGH_MEM_SIZE)) }
        .map_err(|_| "high memory for ACPI tables already set")
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
        command.invoke(&mut EbdaFiles, fwcfg, acpi_digest)?;
    }

    // Safety: we ensure that the RSDP is valid before returning a reference to it.
    let rsdp = unsafe { EBDA.assume_init_mut() };
    rsdp.validate::<P>()?;
    log::info!("ACPI tables before finalizing:");
    debug_print_acpi_tables(rsdp)?;

    log::info!("Finalizing RSDP");
    P::finalize_acpi_tables(rsdp)?;
    rsdp.validate::<P>()?;
    log::info!("ACPI tables after finalizing:");
    debug_print_acpi_tables(rsdp)?;

    Ok(rsdp)
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

#[cfg(test)]
mod tests {
    use core::slice;
    use std::{collections::BTreeMap, ffi::CString};

    use googletest::prelude::*;
    use zeroize::Zeroize;

    use super::*;

    struct TestFirmware;

    impl Firmware for TestFirmware {
        fn find(&mut self, _name: &CStr) -> Option<DirEntry> {
            unimplemented!()
        }

        fn read_file(
            &mut self,
            _file: &DirEntry,
            _buf: &mut [u8],
        ) -> core::result::Result<usize, &'static str> {
            unimplemented!()
        }
    }

    enum TestFile {
        /// File that is actually backed by a chunk of memory and can be read
        /// from/written to.
        BackedFile(Box<[u8]>),

        /// Fake file: just a pointer. Potentially unsafe and must _only_ be
        /// used to look at the address of the file and never dereferenced. This
        /// "fake file" is needed to ensure predictable memory addresses (for
        /// example, if we need to ensure that it's a 16-bit address).
        FakeFile(*mut u8),
    }

    impl From<Box<[u8]>> for TestFile {
        fn from(file: Box<[u8]>) -> Self {
            TestFile::BackedFile(file)
        }
    }

    impl AsRef<[u8]> for TestFile {
        fn as_ref(&self) -> &[u8] {
            match self {
                TestFile::BackedFile(file) => file.as_ref(),
                TestFile::FakeFile(ptr) => {
                    // Safety: it is safe to read (or write) exactly zero bytes to that address.
                    // That is, the slice will be empty, as reading or writing anything would be
                    // unsafe.
                    unsafe { slice::from_raw_parts(*ptr, 0) }
                }
            }
        }
    }

    impl AsMut<[u8]> for TestFile {
        fn as_mut(&mut self) -> &mut [u8] {
            match self {
                TestFile::BackedFile(file) => file.as_mut(),
                TestFile::FakeFile(ptr) => {
                    // Safety: it is safe to read (or write) exactly zero bytes to that address.
                    // That is, the slice will be empty, as reading or writing anything would be
                    // unsafe.
                    unsafe { slice::from_raw_parts_mut(*ptr, 0) }
                }
            }
        }
    }

    #[derive(Default)]
    struct TestFiles {
        files: BTreeMap<CString, TestFile>,
    }

    impl Files for TestFiles {
        fn allocate(
            &mut self,
            name: &CStr,
            layout: Layout,
            _zone: Zone,
        ) -> core::result::Result<&mut [u8], &'static str> {
            if layout.align() != align_of::<u8>() {
                return Err("test allocator doesn't support alignments");
            }
            if self.files.contains_key(name) {
                return Err("file already exists");
            }

            self.files.insert(name.to_owned(), vec![0; layout.size()].into_boxed_slice().into());

            self.get_file_mut(name)
        }

        fn get_file_mut(&mut self, name: &CStr) -> core::result::Result<&mut [u8], &'static str> {
            self.files.get_mut(name).map(AsMut::as_mut).ok_or("file not found")
        }

        fn get_file(&self, name: &CStr) -> core::result::Result<&[u8], &'static str> {
            self.files.get(name).map(AsRef::as_ref).ok_or("file not found")
        }
    }

    impl TestFiles {
        fn new_file(&mut self, name: &CStr, contents: &[u8]) {
            let new_file = self
                .allocate(name, Layout::from_size_align(contents.len(), 1).unwrap(), Zone::FSeg)
                .unwrap();
            new_file.copy_from_slice(contents);
        }

        fn new_file_ptr(
            &mut self,
            name: &CStr,
            ptr: *mut u8,
        ) -> core::result::Result<(), &'static str> {
            if self.files.contains_key(name) {
                return Err("file already exists");
            }
            self.files.insert(name.to_owned(), TestFile::FakeFile(ptr));
            Ok(())
        }
    }

    #[test]
    pub fn test_table_loader_interpretation() {
        let raw = std::fs::read(oak_file_utils::data_path("stage0/testdata/table_loader"))
            .expect("failed to read test data");
        let commands = unsafe {
            core::slice::from_raw_parts(
                raw.as_ptr() as *const _ as *const RomfileCommand,
                raw.len() / core::mem::size_of::<RomfileCommand>(),
            )
        };

        let expected_commands: [RomfileCommand; 20] = [
            Allocate::new("etc/acpi/rsdp", 16, Zone::FSeg).into(),
            Allocate::new("etc/acpi/tables", 64, Zone::High).into(),
            AddChecksum::new("etc/acpi/tables", 73, 64, 8293).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8393, 4).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8397, 4).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8497, 8).into(),
            AddChecksum::new("etc/acpi/tables", 8366, 8357, 244).into(),
            AddChecksum::new("etc/acpi/tables", 8610, 8601, 120).into(),
            AddChecksum::new("etc/acpi/tables", 8730, 8721, 56).into(),
            AddChecksum::new("etc/acpi/tables", 8786, 8777, 60).into(),
            AddChecksum::new("etc/acpi/tables", 8846, 8837, 40).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8913, 4).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8917, 4).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8921, 4).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8925, 4).into(),
            AddPointer::new("etc/acpi/tables", "etc/acpi/tables", 8929, 4).into(),
            AddChecksum::new("etc/acpi/tables", 8886, 8877, 56).into(),
            AddPointer::new("etc/acpi/rsdp", "etc/acpi/tables", 16, 4).into(),
            AddChecksum::new("etc/acpi/rsdp", 8, 0, 20).into(),
            RomfileCommand::default(),
        ];

        assert_eq!(commands, &expected_commands[..]);
    }

    #[test]
    pub fn test_add_checksum() {
        let mut files = TestFiles::default();
        let mut digest = Sha256::default();

        files.new_file(
            c"test",
            &[0xD4, 0x0A, 0x1B, 0x73, 0x0F, 0x3A, 0x0F, 0x41, 0x00, 0xA7, 0x0A, 0x14, 0x00],
        );

        AddChecksum::new("test", 12, 0, 12)
            .invoke(&mut files, &mut TestFirmware, &mut digest)
            .expect("failed to compute checksum");

        assert_that!(
            files.get_file(c"test"),
            ok(eq(&[0xD4, 0x0A, 0x1B, 0x73, 0x0F, 0x3A, 0x0F, 0x41, 0x00, 0xA7, 0x0A, 0x14, 0x36]))
        );
    }

    #[gtest]
    pub fn test_add_checksum_simple() {
        let mut files = TestFiles::default();
        let mut digest = Sha256::default();

        // File does not exist.
        expect_that!(
            AddChecksum::new("test", 12, 0, 12).invoke(&mut files, &mut TestFirmware, &mut digest),
            err(anything())
        );

        files.new_file(c"test", &[0x00, 0x00, 0x00, 0x00]);

        // Offset past the end of file.
        expect_that!(
            AddChecksum::new("test", 4, 0, 3).invoke(&mut files, &mut TestFirmware, &mut digest),
            err(anything())
        );

        // Start past the end of file.
        expect_that!(
            AddChecksum::new("test", 3, 4, 1).invoke(&mut files, &mut TestFirmware, &mut digest),
            err(anything())
        );

        // Offset would read beyond the file.
        expect_that!(
            AddChecksum::new("test", 0, 3, 2).invoke(&mut files, &mut TestFirmware, &mut digest),
            err(anything())
        );

        // Finally, a basic success test (although we don't check the result)
        expect_that!(
            AddChecksum::new("test", 0, 1, 3).invoke(&mut files, &mut TestFirmware, &mut digest),
            ok(())
        );

        expect_that!(
            AddChecksum::new("test", 3, 0, 3).invoke(&mut files, &mut TestFirmware, &mut digest),
            ok(())
        );
    }

    #[gtest]
    pub fn test_add_pointer() {
        let mut files = TestFiles::default();
        let mut digest = Sha256::default();

        // Obviously we have no idea where exactly that file lands so we need to
        // dynamically determine its location.
        // The file size is 8 bytes, so it'll fit any 64-bit address.
        files.new_file(c"test", &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
        let address = files.get_file(c"test").unwrap().as_ptr() as usize;

        // Check 1: can we just write our own address?
        AddPointer::new("test", "test", 0, 8)
            .invoke(&mut files, &mut TestFirmware, &mut digest)
            .expect("failed to add pointer");

        let expected = address.to_le_bytes();
        expect_that!(files.get_file(c"test"), ok(eq(&expected[..])));

        // Check 2: are offsets respected?
        let offset: usize = 0x030201;
        files.get_file_mut(c"test").unwrap().copy_from_slice(&offset.to_le_bytes());

        let expected = (address + offset).to_le_bytes();
        AddPointer::new("test", "test", 0, 8)
            .invoke(&mut files, &mut TestFirmware, &mut digest)
            .expect("failed to add pointer");
        expect_that!(files.get_file(c"test"), ok(eq(&expected[..])));

        let address: usize = 0xAABBCCDD;
        files.new_file_ptr(c"32bit", address as *mut u8).unwrap();

        // Check 3: store a most definitely 32-bit address and see that it works.
        files.get_file_mut(c"test").unwrap().zeroize();
        AddPointer::new("test", "32bit", 0, 8)
            .invoke(&mut files, &mut TestFirmware, &mut digest)
            .expect("failed to add pointer");
        expect_that!(files.get_file(c"test"), ok(eq(&address.to_le_bytes()[..])));

        // Check 4: write that address to just 4 bytes -- the last 4 bytes to make it
        // complicated.
        files.get_file_mut(c"test").unwrap().zeroize();
        let expected: [u8; 8] = [0x00, 0x00, 0x00, 0x00, 0xDD, 0xCC, 0xBB, 0xAA];
        AddPointer::new("test", "32bit", 4, 4)
            .invoke(&mut files, &mut TestFirmware, &mut digest)
            .expect("failed to add pointer");
        expect_that!(files.get_file(c"test"), ok(eq(&expected[..])));
    }
}
