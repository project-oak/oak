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

use elf::{
    ElfBytes,
    abi::{PF_X, PT_LOAD},
    endian::AnyEndian,
    segment::ProgramHeader,
};
use oak_linux_boot_params::{BootE820Entry, E820EntryType, Ramdisk};
use x86_64::{
    PhysAddr, VirtAddr,
    instructions::tlb::flush_all,
    registers::control::Cr3,
    structures::paging::{
        PageSize, PageTable, PageTableFlags, Size1GiB, Size2MiB, Size4KiB,
        page_table::PageTableLevel,
    },
};

// We assume Stage 0 created an identity map for the first 1GiB of memory.
const TOP_OF_VIRTUAL_MEMORY: u64 = Size1GiB::SIZE;

// Mask for extracting a 4KiB-aligned physical address (bits 50..12) from a
// page table entry's address while ignoring the AMD SEV encrypted C-bit
// (bit 51).
const PAGE_TABLE_ADDRESS_MASK: u64 = 0x0007_FFFF_FFFF_F000;

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

/// Clears `NO_EXECUTE` on the identity-mapped page table entries covering
/// `[start, start + size)`, supporting 1GiB, 2MiB, and 4KiB page mappings.
fn make_executable(start: VirtAddr, size: usize) {
    let (pml4_frame, _) = Cr3::read();
    make_executable_with_pml4(pml4_frame.start_address(), start, size, phys_to_virt);
    flush_all();
}

fn make_executable_with_pml4(
    pml4_addr: PhysAddr,
    start: VirtAddr,
    size: usize,
    phys_to_virt: impl Fn(PhysAddr) -> VirtAddr,
) {
    let pml4_addr = PhysAddr::new(pml4_addr.as_u64() & PAGE_TABLE_ADDRESS_MASK);
    let mut addr = start.align_down(Size4KiB::SIZE);
    let end = (start + size as u64).align_up(Size4KiB::SIZE);
    while addr < end {
        let mut table_addr = pml4_addr;
        let mut level = PageTableLevel::Four;
        let step = loop {
            assert!(
                table_addr.as_u64() < TOP_OF_VIRTUAL_MEMORY,
                "page table address falls above mapped virtual memory"
            );
            // Safety: the bootloader sets up an identity mapping for the lower
            // memory containing the page tables. `PageTableEntry::set_flags`
            // preserves bits 12..=51 via `PageTableEntry::addr()`, keeping any
            // platform memory encryption bit intact.
            let table = unsafe { &mut *phys_to_virt(table_addr).as_mut_ptr::<PageTable>() };
            let entry = &mut table[addr.page_table_index(level)];
            assert!(
                entry.flags().contains(PageTableFlags::PRESENT),
                "page table entry is not present"
            );
            let entry_addr = PhysAddr::new(entry.addr().as_u64() & PAGE_TABLE_ADDRESS_MASK);
            let Some(next_level) = level
                .next_lower_level()
                .filter(|_| !entry.flags().contains(PageTableFlags::HUGE_PAGE))
            else {
                assert!(level != PageTableLevel::Four, "huge page flag is not valid on PML4 entry");
                let step = level.entry_address_space_alignment();
                assert_eq!(
                    entry_addr.as_u64(),
                    addr.align_down(step).as_u64(),
                    "page table entry is not an identity mapping"
                );
                if entry.flags().contains(PageTableFlags::NO_EXECUTE) {
                    entry.set_flags(entry.flags() - PageTableFlags::NO_EXECUTE);
                }
                break step;
            };
            if entry.flags().contains(PageTableFlags::NO_EXECUTE) {
                entry.set_flags(entry.flags() - PageTableFlags::NO_EXECUTE);
            }
            table_addr = entry_addr;
            level = next_level;
        };
        addr = addr.align_down(step) + step;
    }
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
    // Using manual `for` loop rather than fill to avoid the compiler's intrinsic
    // function which uses an indirect call via the PLT.
    for item in &mut *target {
        *item = 0;
    }

    // Manually copy between slices to avoid the compiler's intrinsic memcpy which
    // uses an indirect call via the PLT.
    #[allow(clippy::manual_memcpy)]
    {
        for i in 0..file_length {
            target[i] = source[i]
        }
    }
    if phdr.p_flags & PF_X != 0 {
        make_executable(start_address, size);
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
            && entry.end() as u64 >= end.as_u64()
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

#[cfg(test)]
mod tests {
    use std::boxed::Box;

    use googletest::prelude::*;
    use x86_64::structures::paging::PageTableIndex;

    use super::*;

    const PML4_INDEX: usize = 1;
    const PDPT_INDEX: usize = 2;
    const PD_INDEX: usize = 3;
    const PT_INDEX: usize = 4;
    const SEV_C_BIT: u64 = 1 << 51;

    struct TestPageTables {
        tables: Box<[PageTable; 8]>,
    }

    impl TestPageTables {
        fn new() -> Self {
            Self { tables: Box::new([const { PageTable::new() }; 8]) }
        }

        fn table_addr(&self, index: usize) -> PhysAddr {
            PhysAddr::new((index as u64) * Size4KiB::SIZE)
        }

        fn table(&self, index: usize) -> &PageTable {
            &self.tables[index]
        }

        fn table_mut(&mut self, index: usize) -> &mut PageTable {
            &mut self.tables[index]
        }

        fn phys_to_virt(&mut self) -> impl Fn(PhysAddr) -> VirtAddr + '_ {
            let base = self.tables.as_mut_ptr() as u64;
            move |pa: PhysAddr| {
                let index = (pa.as_u64() / Size4KiB::SIZE) as usize;
                assert!(index < 8, "out of bounds test table access at {pa:?}");
                VirtAddr::new(base + pa.as_u64())
            }
        }
    }

    #[googletest::test]
    fn make_executable_4k_pages() {
        let mut tables = TestPageTables::new();
        let pml4_addr = tables.table_addr(PML4_INDEX);
        let pdpt_addr = tables.table_addr(PDPT_INDEX);
        let pd_addr = tables.table_addr(PD_INDEX);
        let pt_addr = tables.table_addr(PT_INDEX);

        let nx_rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        tables.table_mut(PML4_INDEX)[0].set_addr(pdpt_addr, nx_rw);
        tables.table_mut(PDPT_INDEX)[0].set_addr(pd_addr, nx_rw);
        tables.table_mut(PD_INDEX)[1].set_addr(pt_addr, nx_rw);
        for i in 0..4u16 {
            let frame_addr = PhysAddr::new(Size2MiB::SIZE + (i as u64) * Size4KiB::SIZE);
            tables.table_mut(PT_INDEX)[PageTableIndex::new(i)].set_addr(frame_addr, nx_rw);
        }

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE + Size4KiB::SIZE),
            (Size4KiB::SIZE as usize) + 100,
            tables.phys_to_virt(),
        );

        let rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
        assert_that!(tables.table(PML4_INDEX)[0].flags(), eq(rw));
        assert_that!(tables.table(PDPT_INDEX)[0].flags(), eq(rw));
        assert_that!(tables.table(PD_INDEX)[1].flags(), eq(rw));
        assert_that!(tables.table(PT_INDEX)[0].flags(), eq(nx_rw));
        assert_that!(tables.table(PT_INDEX)[1].flags(), eq(rw));
        assert_that!(tables.table(PT_INDEX)[2].flags(), eq(rw));
        assert_that!(tables.table(PT_INDEX)[3].flags(), eq(nx_rw));
    }

    #[googletest::test]
    fn make_executable_2m_huge_pages() {
        let mut tables = TestPageTables::new();
        let pml4_addr = tables.table_addr(PML4_INDEX);
        let pdpt_addr = tables.table_addr(PDPT_INDEX);
        let pd_addr = tables.table_addr(PD_INDEX);

        let nx_rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        let nx_huge = nx_rw | PageTableFlags::HUGE_PAGE;
        tables.table_mut(PML4_INDEX)[0].set_addr(pdpt_addr, nx_rw);
        tables.table_mut(PDPT_INDEX)[0].set_addr(pd_addr, nx_rw);
        for i in 0..4u16 {
            let frame_addr = PhysAddr::new((i as u64) * Size2MiB::SIZE);
            tables.table_mut(PD_INDEX)[PageTableIndex::new(i)].set_addr(frame_addr, nx_huge);
        }

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE),
            (Size2MiB::SIZE as usize) + 4096,
            tables.phys_to_virt(),
        );

        let rw_huge =
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE;
        assert_that!(tables.table(PD_INDEX)[0].flags(), eq(nx_huge));
        assert_that!(tables.table(PD_INDEX)[1].flags(), eq(rw_huge));
        assert_that!(tables.table(PD_INDEX)[2].flags(), eq(rw_huge));
        assert_that!(tables.table(PD_INDEX)[3].flags(), eq(nx_huge));
    }

    #[googletest::test]
    fn make_executable_1g_huge_page() {
        let mut tables = TestPageTables::new();
        let pml4_addr = tables.table_addr(PML4_INDEX);
        let pdpt_addr = tables.table_addr(PDPT_INDEX);

        let nx_rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        let nx_huge = nx_rw | PageTableFlags::HUGE_PAGE;
        tables.table_mut(PML4_INDEX)[0].set_addr(pdpt_addr, nx_rw);
        tables.table_mut(PDPT_INDEX)[0].set_addr(PhysAddr::new(0), nx_huge);

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            tables.phys_to_virt(),
        );

        let rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
        assert_that!(tables.table(PML4_INDEX)[0].flags(), eq(rw));
        assert_that!(tables.table(PDPT_INDEX)[0].flags(), eq(rw | PageTableFlags::HUGE_PAGE));
    }

    #[googletest::test]
    fn make_executable_preserves_sev_c_bit() {
        let mut tables = TestPageTables::new();
        let pml4_addr = PhysAddr::new(tables.table_addr(PML4_INDEX).as_u64() | SEV_C_BIT);
        let pdpt_addr = PhysAddr::new(tables.table_addr(PDPT_INDEX).as_u64() | SEV_C_BIT);
        let pd_addr = PhysAddr::new(tables.table_addr(PD_INDEX).as_u64() | SEV_C_BIT);

        let nx_rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        let nx_huge = nx_rw | PageTableFlags::HUGE_PAGE;
        tables.table_mut(PML4_INDEX)[0].set_addr(pdpt_addr, nx_rw);
        tables.table_mut(PDPT_INDEX)[0].set_addr(pd_addr, nx_rw);
        let leaf_addr = PhysAddr::new(Size2MiB::SIZE | SEV_C_BIT);
        tables.table_mut(PD_INDEX)[1].set_addr(leaf_addr, nx_huge);

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            tables.phys_to_virt(),
        );

        let rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
        assert_that!(tables.table(PML4_INDEX)[0].flags(), eq(rw));
        assert_that!(tables.table(PML4_INDEX)[0].addr(), eq(pdpt_addr));
        assert_that!(tables.table(PDPT_INDEX)[0].flags(), eq(rw));
        assert_that!(tables.table(PDPT_INDEX)[0].addr(), eq(pd_addr));
        assert_that!(tables.table(PD_INDEX)[1].flags(), eq(rw | PageTableFlags::HUGE_PAGE));
        assert_that!(tables.table(PD_INDEX)[1].addr(), eq(leaf_addr));
    }

    #[googletest::test]
    #[should_panic(expected = "page table entry is not an identity mapping")]
    fn make_executable_panics_on_non_identity_mapping() {
        let mut tables = TestPageTables::new();
        let pml4_addr = tables.table_addr(PML4_INDEX);
        let pdpt_addr = tables.table_addr(PDPT_INDEX);
        let pd_addr = tables.table_addr(PD_INDEX);

        let nx_rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        tables.table_mut(PML4_INDEX)[0].set_addr(pdpt_addr, nx_rw);
        tables.table_mut(PDPT_INDEX)[0].set_addr(pd_addr, nx_rw);
        // Map virtual 2MiB (PD[1]) to physical 4MiB instead of 2MiB.
        tables.table_mut(PD_INDEX)[1]
            .set_addr(PhysAddr::new(2 * Size2MiB::SIZE), nx_rw | PageTableFlags::HUGE_PAGE);

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            tables.phys_to_virt(),
        );
    }

    #[googletest::test]
    #[should_panic(expected = "page table entry is not present")]
    fn make_executable_panics_on_unmapped_entry() {
        let mut tables = TestPageTables::new();
        let pml4_addr = tables.table_addr(PML4_INDEX);
        let pdpt_addr = tables.table_addr(PDPT_INDEX);
        let pd_addr = tables.table_addr(PD_INDEX);

        let rw = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;
        tables.table_mut(PML4_INDEX)[0].set_addr(pdpt_addr, rw);
        tables.table_mut(PDPT_INDEX)[0].set_addr(pd_addr, rw);
        // Leave PD[1] not present.

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            tables.phys_to_virt(),
        );
    }

    #[googletest::test]
    #[should_panic(expected = "huge page flag is not valid on PML4 entry")]
    fn make_executable_panics_on_pml4_huge_page() {
        let mut tables = TestPageTables::new();
        let pml4_addr = tables.table_addr(PML4_INDEX);
        let pdpt_addr = tables.table_addr(PDPT_INDEX);

        tables.table_mut(PML4_INDEX)[0].set_addr(
            pdpt_addr,
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
        );

        make_executable_with_pml4(
            pml4_addr,
            VirtAddr::new(Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            tables.phys_to_virt(),
        );
    }

    #[googletest::test]
    #[should_panic(expected = "page table address falls above mapped virtual memory")]
    fn make_executable_panics_on_table_above_virtual_memory() {
        let mut tables = TestPageTables::new();
        make_executable_with_pml4(
            PhysAddr::new(TOP_OF_VIRTUAL_MEMORY),
            VirtAddr::new(Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            tables.phys_to_virt(),
        );
    }
}
