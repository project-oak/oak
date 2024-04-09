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

use alloc::boxed::Box;
use core::ptr::addr_of_mut;

use oak_core::sync::OnceCell;
use spinning_top::Spinlock;
use x86_64::{
    instructions::tlb::flush_all,
    structures::paging::{page_table::PageTableFlags, PageSize, PageTable, Size2MiB, Size4KiB},
    PhysAddr,
};

use crate::BOOT_ALLOC;

pub static mut PML4: PageTable = PageTable::new();
pub static mut PDPT: PageTable = PageTable::new();
pub static mut PD_0: PageTable = PageTable::new();
pub static mut PD_3: PageTable = PageTable::new();

/// Wrapper for the page table references so that we can access them via a mutex
/// rather than directly via unsafe code.
#[repr(C, align(4096))]
pub struct PageTableRefs {
    /// The root page-map level 4 table coverting virtual memory ranges
    /// 0..128TiB and (16EiB-128TiB)..16EiB.
    pub pml4: &'static mut PageTable,

    /// The page-directory pointer table covering virtual memory range
    /// 0..512GiB.
    pub pdpt: &'static mut PageTable,

    /// The page directory covering virtual memory range 0..1GiB.
    pub pd_0: &'static mut PageTable,

    /// The page directory covering virtual memory range 3..4GiB.
    pub pd_3: &'static mut PageTable,

    /// The page table covering virtual memory range 0..2MiB where we want 4KiB
    /// pages.
    pub pt_0: &'static mut PageTable,
}

/// References to all the pages tables we care about.
pub static PAGE_TABLE_REFS: OnceCell<Spinlock<PageTableRefs>> = OnceCell::new();

/// Initialises the page table references.
pub fn init_page_table_refs(encrypted: u64) {
    // Safety: accessing the mutable statics here is safe since we only do it once
    // and protect the mutable references with a mutex. This function can only
    // be called once, since updating `PAGE_TABLE_REFS` twice will panic.
    let pml4 = unsafe { &mut *addr_of_mut!(PML4) };
    let pdpt = unsafe { &mut *addr_of_mut!(PDPT) };
    let pd_0 = unsafe { &mut *addr_of_mut!(PD_0) };
    let pd_3 = unsafe { &mut *addr_of_mut!(PD_3) };

    // Set up a new page table that maps the first 2MiB as 4KiB pages, so that we
    // can share individual 4KiB pages with the hypervisor as needed. We are
    // using an identity mapping between virtual and physical addresses.
    let pt_0 = Box::leak(Box::new_in(PageTable::new(), &BOOT_ALLOC));
    pt_0.iter_mut().enumerate().skip(1).for_each(|(i, entry)| {
        entry.set_addr(
            PhysAddr::new(((i as u64) * Size4KiB::SIZE) | encrypted),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
        );
    });
    pd_0[0].set_addr(
        PhysAddr::new(pt_0 as *const _ as usize as u64 | encrypted),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );

    let page_tables = PageTableRefs { pml4, pdpt, pd_0, pd_3, pt_0 };

    if PAGE_TABLE_REFS.set(Spinlock::new(page_tables)).is_err() {
        panic!("page table wrapper already initialized");
    }

    flush_all();
}

/// Maps the first 1GiB of memory using 2MiB hugepages, except for the first
/// 2MiB that was already mapped as 512 4KiB pages.
pub fn map_additional_memory(encrypted: u64) {
    {
        let mut page_tables = PAGE_TABLE_REFS.get().expect("page tables not initiallized").lock();
        let pd = &mut page_tables.pd_0;
        pd.iter_mut().enumerate().skip(1).for_each(|(i, entry)| {
            entry.set_addr(
                PhysAddr::new(((i as u64) * Size2MiB::SIZE) | encrypted),
                PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
            );
        });
    }

    flush_all();
}

// Remaps the first 2MiB of memory, which was previously mapped as 512 4KiB
// pages, as a single 2MiB huge page again.
pub fn remap_first_huge_page(encrypted: u64) {
    {
        let mut page_tables = PAGE_TABLE_REFS.get().expect("page tables not initiallized").lock();
        let pd = &mut page_tables.pd_0;

        // Allow identity-op to keep the fact that the address we're talking about here
        // is 0x00.
        #[allow(clippy::identity_op)]
        pd[0].set_addr(
            PhysAddr::new(0x0 | encrypted),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
        );
    }

    flush_all();
}
