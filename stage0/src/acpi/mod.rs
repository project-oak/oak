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

//! This module provides functions to build ACPI tables content from commands
//! received from the VMM.

// These data structures (and constants) are derived from
// qemu/hw/acpi/bios-linker-loader.c that defines the interface.

use core::{ffi::CStr, mem::MaybeUninit, ops::Deref};

use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use sha2::{Digest, Sha256};
use strum::FromRepr;

use crate::{
    acpi_tables::{
        DescriptionHeader, MultiprocessorWakeup, ProcessorLocalApic, ProcessorLocalX2Apic, Rsdp,
    },
    fw_cfg::FwCfg,
    pci::PciWindows,
    Fadt, Madt, ZeroPage,
};

mod commands;
mod files;
use commands::{Invoke, RomfileCommand};
use files::{Files, MemFiles};

type LowMemoryAllocator = linked_list_allocator::LockedHeap;
/// Allocator for low memory in the EBDA: 128K of memory (where the RSDP will be
/// loaded).
static LOW_MEMORY_ALLOCATOR: LowMemoryAllocator = LowMemoryAllocator::empty();

/// EDBA is 128 KiB (0x2_0000).
#[link_section = ".ebda"]
static mut EBDA: [MaybeUninit<u8>; 0x2_0000] = [MaybeUninit::uninit(); 0x2_0000];

/// How much memory to reserve for ACPI tables in "high" memory.
const HIGH_MEM_SIZE: usize = 0x10_0000;

// Not using BumpAllocator here because we don't statically know where the
// memory backing the allocator will go.
type HighMemoryAllocator = linked_list_allocator::LockedHeap;
/// Allocator for high memory (where the ACPI tables themselves will go).
pub static HIGH_MEMORY_ALLOCATOR: HighMemoryAllocator = HighMemoryAllocator::empty();

const TABLE_LOADER_FILE_NAME: &CStr = c"etc/table-loader";

#[repr(u8)]
#[derive(Debug, FromRepr)]
pub enum Zone {
    High = 1,
    FSeg = 2,
}

pub fn setup_low_allocator(zero_page: &mut ZeroPage) -> Result<(), &'static str> {
    // Safety: Access is safe since we don't support threads, so there is no
    // concurrent access.
    let edba_slice = unsafe { EBDA.as_mut_slice() };
    // Reserve the memory for ACPI tables.
    zero_page.insert_e820_entry(BootE820Entry::new(
        edba_slice.as_ptr() as usize,
        edba_slice.len(),
        E820EntryType::ACPI,
    ));
    LOW_MEMORY_ALLOCATOR.lock().init_from_slice(edba_slice);
    Ok(())
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
            .next_back()
            .ok_or("could not find memory for ACPI tables")?;
        let mem_end = core::cmp::min(0x4000_0000, entry.addr() + entry.size());
        mem_end - HIGH_MEM_SIZE
    };
    // reserve the memory for ACPI tables
    zero_page.insert_e820_entry(BootE820Entry::new(mem_start, HIGH_MEM_SIZE, E820EntryType::ACPI));

    // Safety: the pointer is not null, we've reserved the 'static memory for
    // ourselves.
    unsafe {
        HIGH_MEMORY_ALLOCATOR.lock().init(mem_start as *mut u8, HIGH_MEM_SIZE);
    }
    Ok(())
}

/// Populates the ACPI tables per linking instructions in `etc/table-loader`.
///
/// Returns the address of the RSDP table.
pub fn build_acpi_tables<P: crate::Platform>(
    fwcfg: &mut FwCfg<P>,
    acpi_digest: &mut Sha256,
    pci_windows: Option<PciWindows>,
) -> Result<&'static Rsdp, &'static str> {
    let mut files = MemFiles::new(&LOW_MEMORY_ALLOCATOR, &HIGH_MEMORY_ALLOCATOR);

    let file =
        fwcfg.find(TABLE_LOADER_FILE_NAME).ok_or("Could not find 'etc/table-loader' in fw_cfg")?;

    if file.size() % core::mem::size_of::<RomfileCommand>() != 0 {
        return Err("length of 'etc/table-loader' is not a multiple of command struct size");
    }

    let buf = fwcfg.read_file_vec(&file)?;
    acpi_digest.update(&buf);

    // We can't use zerocopy::FromBytes/IntoBytes here, as the fields of the structs
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
        command.invoke(&mut files, fwcfg, pci_windows.as_ref(), acpi_digest)?;
    }

    // Strictly speaking we should search through the low memory to find the RSDP,
    // but for practical purposes we know that the VMs we care about end the file
    // that contains the file with `acpi/rsdp` (the prefix may vary), so let's look
    // up just that file.
    let rsdp = files.find_file_suffix(c"acpi/rsdp").ok_or("RSDP file not found")?;

    // Safety: we ensure that the RSDP is valid before returning a reference to it.
    let rsdp = unsafe { &mut *(rsdp.as_ptr() as *mut Rsdp) };
    rsdp.validate::<P>()?;
    log::info!("ACPI tables before finalizing:");
    debug_print_acpi_tables(rsdp)?;

    log::info!("Finalizing RSDP");
    P::finalize_acpi_tables(rsdp)?;
    rsdp.validate::<P>()?;
    log::info!("ACPI tables after finalizing:");
    debug_print_acpi_tables(rsdp)?;

    // Ensure the tables stick around by leaking the memory holding them.
    files.leak();

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
        // FADT is always guaranteed in the RSDT/XSDT as per ACPI spec:
        // https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html#overview-of-the-system-description-table-architecture
        if header.signature == *Fadt::SIGNATURE {
            let fadt = Fadt::new(header)?;
            log::info!("FADT: {:?}", fadt);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::ptr::NonNull;

    use googletest::prelude::*;
    use zeroize::Zeroize;

    use super::{commands::*, *};
    use crate::fw_cfg::{DirEntry, Firmware};

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

    type TestFiles = MemFiles<std::alloc::Global, std::alloc::Global>;

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

        println!(" COMMAND 0: {:?}", commands[0]);
        println!("ECOMMAND 0: {:?}", &expected_commands[0]);
        assert_that!(&commands[0], eq(&expected_commands[0]));
        assert_that!(commands, container_eq(expected_commands));
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
            .invoke(&mut files, &mut TestFirmware, None, &mut digest)
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
            AddChecksum::new("test", 12, 0, 12).invoke(
                &mut files,
                &mut TestFirmware,
                None,
                &mut digest
            ),
            err(anything())
        );

        files.new_file(c"test", &[0x00, 0x00, 0x00, 0x00]);

        // Offset past the end of file.
        expect_that!(
            AddChecksum::new("test", 4, 0, 3).invoke(
                &mut files,
                &mut TestFirmware,
                None,
                &mut digest
            ),
            err(anything())
        );

        // Start past the end of file.
        expect_that!(
            AddChecksum::new("test", 3, 4, 1).invoke(
                &mut files,
                &mut TestFirmware,
                None,
                &mut digest
            ),
            err(anything())
        );

        // Offset would read beyond the file.
        expect_that!(
            AddChecksum::new("test", 0, 3, 2).invoke(
                &mut files,
                &mut TestFirmware,
                None,
                &mut digest
            ),
            err(anything())
        );

        // Finally, a basic success test (although we don't check the result)
        expect_that!(
            AddChecksum::new("test", 0, 1, 3).invoke(
                &mut files,
                &mut TestFirmware,
                None,
                &mut digest
            ),
            ok(())
        );

        expect_that!(
            AddChecksum::new("test", 3, 0, 3).invoke(
                &mut files,
                &mut TestFirmware,
                None,
                &mut digest
            ),
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
            .invoke(&mut files, &mut TestFirmware, None, &mut digest)
            .expect("failed to add pointer");

        let expected = address.to_le_bytes();
        expect_that!(files.get_file(c"test"), ok(eq(&expected[..])));

        // Check 2: are offsets respected?
        let offset: usize = 0x030201;
        files.get_file_mut(c"test").unwrap().copy_from_slice(&offset.to_le_bytes());

        let expected = (address + offset).to_le_bytes();
        AddPointer::new("test", "test", 0, 8)
            .invoke(&mut files, &mut TestFirmware, None, &mut digest)
            .expect("failed to add pointer");
        expect_that!(files.get_file(c"test"), ok(eq(&expected[..])));

        let address: usize = 0xAABBCCDD;
        files.new_file_ptr(c"32bit", NonNull::new(address as *mut u8).unwrap()).unwrap();

        // Check 3: store a most definitely 32-bit address and see that it works.
        files.get_file_mut(c"test").unwrap().zeroize();
        AddPointer::new("test", "32bit", 0, 8)
            .invoke(&mut files, &mut TestFirmware, None, &mut digest)
            .expect("failed to add pointer");
        expect_that!(files.get_file(c"test"), ok(eq(&address.to_le_bytes()[..])));

        // Check 4: write that address to just 4 bytes -- the last 4 bytes to make it
        // complicated.
        files.get_file_mut(c"test").unwrap().zeroize();
        let expected: [u8; 8] = [0x00, 0x00, 0x00, 0x00, 0xDD, 0xCC, 0xBB, 0xAA];
        AddPointer::new("test", "32bit", 4, 4)
            .invoke(&mut files, &mut TestFirmware, None, &mut digest)
            .expect("failed to add pointer");
        expect_that!(files.get_file(c"test"), ok(eq(&expected[..])));
    }
}
