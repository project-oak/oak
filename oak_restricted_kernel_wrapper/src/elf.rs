//
// Copyright 2023 The Project Oak Authors
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

use core::slice;

use elf::{ElfBytes, abi::PT_LOAD, endian::AnyEndian, segment::ProgramHeader};
use oak_linux_boot_params::{BootE820Entry, E820EntryType, Ramdisk};
use x86_64::{
    PhysAddr, VirtAddr,
    structures::paging::{PageSize, Size1GiB, Size2MiB},
};

// We assume Stage 0 created an identity map for the first 1GiB of memory.
const TOP_OF_VIRTUAL_MEMORY: u64 = Size1GiB::SIZE;

/// Parses an ELF file and lays it out in memory.
///
/// Returns the entry point.
pub fn parse_elf_file(
    buf: &[u8],
    e820_table: &[BootE820Entry],
    ramdisk: Option<Ramdisk>,
) -> VirtAddr {
    let file = ElfBytes::<AnyEndian>::minimal_parse(buf).expect("couldn't parse kernel header");

    for ref phdr in file
        .segments()
        .expect("couldn't parse ELF program headers")
        .iter()
        .filter(|&phdr| phdr.p_type == PT_LOAD)
    {
        load_segment(phdr, buf, e820_table, &ramdisk).unwrap();
    }

    phys_to_virt(PhysAddr::new(file.ehdr.e_entry))
}

/// Loads a segment from an ELF file into memory.
fn load_segment(
    phdr: &ProgramHeader,
    buf: &[u8],
    e820_table: &[BootE820Entry],
    ramdisk: &Option<Ramdisk>,
) -> Result<(), &'static str> {
    let file_offset = phdr.p_offset as usize;
    let file_length = phdr.p_filesz as usize;
    let source = &buf[file_offset..file_offset + file_length];
    let start_address = phys_to_virt(PhysAddr::new(phdr.p_paddr));
    let size = phdr.p_memsz as usize;
    check_memory(start_address, size, e820_table)?;
    check_non_overlapping(start_address, size, VirtAddr::from_ptr(buf.as_ptr()), buf.len())
        .map_err(|_| "region overlaps with ELF file")?;
    if let Some(ramdisk) = ramdisk {
        check_non_overlapping(
            start_address,
            size,
            phys_to_virt(PhysAddr::new(ramdisk.addr.into())),
            ramdisk.size as usize,
        )
        .map_err(|_| "region overlaps with ramdisk")?
    };
    // Safety: we checked that the target memory is valid and that it does not
    // overlap with the source buffer.
    let target = unsafe { slice::from_raw_parts_mut::<u8>(start_address.as_mut_ptr(), size) };

    // Zero out the target in case the file content is shorter than the target.
    target.fill(0);

    // Manually copy between slices to avoid the compiler's intrinsic memcpy which
    // uses an indirect call via the PLT.
    #[allow(clippy::manual_memcpy)]
    {
        for i in 0..file_length {
            target[i] = source[i]
        }
    }
    Ok(())
}

/// Makes sure that a chunk of memory is valid
pub fn check_memory(
    start: VirtAddr,
    size: usize,
    e820_table: &[BootE820Entry],
) -> Result<(), &'static str> {
    let end = start + (size as u64);
    if start.as_u64() < Size2MiB::SIZE {
        return Err("address falls in the first 2MiB");
    }
    if end.as_u64() > TOP_OF_VIRTUAL_MEMORY {
        return Err("region ends above the mapped virtual memory");
    }
    if !e820_table.iter().any(|entry| {
        entry.entry_type() == Some(E820EntryType::RAM)
            && entry.addr() as u64 <= start.as_u64()
            && (entry.addr() + entry.size()) as u64 >= end.as_u64()
    }) {
        return Err("region is not backed by physical memory");
    }

    Ok(())
}

/// Ensures that two ranges don't overlap.
fn check_non_overlapping(
    range_1_start: VirtAddr,
    range_1_size: usize,
    range_2_start: VirtAddr,
    range_2_size: usize,
) -> Result<(), &'static str> {
    let range_1_end = range_1_start + (range_1_size as u64);
    let range_2_end = range_2_start + (range_2_size as u64);
    if range_1_start < range_2_end && range_1_end > range_2_start {
        return Err("regions overlap");
    }
    Ok(())
}

fn phys_to_virt(address: PhysAddr) -> VirtAddr {
    // We assume an identity mapping throughout.
    VirtAddr::new(address.as_u64())
}
