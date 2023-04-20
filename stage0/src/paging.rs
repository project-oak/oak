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

use core::mem::MaybeUninit;
use oak_core::sync::OnceCell;
use spinning_top::Spinlock;
use x86_64::{
    instructions::tlb::flush_all,
    structures::paging::{page_table::PageTableFlags, PageSize, PageTable, Size2MiB},
    PhysAddr,
};

#[link_section = ".boot"]
pub static mut PML4: MaybeUninit<PageTable> = MaybeUninit::uninit();

#[link_section = ".boot"]
pub static mut PDPT: MaybeUninit<PageTable> = MaybeUninit::uninit();

#[link_section = ".boot"]
pub static mut PD_0: MaybeUninit<PageTable> = MaybeUninit::uninit();

#[link_section = ".boot"]
pub static mut PD_3: MaybeUninit<PageTable> = MaybeUninit::uninit();

#[link_section = ".boot"]
pub static mut PT_0: MaybeUninit<PageTable> = MaybeUninit::uninit();

/// Wrapper for the page table references so that we can access them via a mutex rather than
/// directly via unsafe code.
#[repr(C, align(4096))]
pub struct PageTableRefs {
    /// The root page-map level 4 table coverting virtual memory ranges 0..128TiB and
    /// (16EiB-128TiB)..16EiB.
    pub pml4: &'static mut PageTable,

    /// The page-directory pointer table covering virtual memory range 0..512GiB.
    pub pdpt: &'static mut PageTable,

    /// The page directory covering virtual memory range 0..1GiB.
    pub pd_0: &'static mut PageTable,

    /// The page directory covering virtual memory range 3..4GiB.
    pub pd_3: &'static mut PageTable,

    /// The page table covering virtual memory rane 0..2MiB where we want 4KiB pages.
    pub pt_0: &'static mut PageTable,
}

/// References to all the pages tables we care about.
pub static PAGE_TABLE_REFS: OnceCell<Spinlock<PageTableRefs>> = OnceCell::new();

/// Initialises the page table references.
pub fn init_page_table_refs() {
    // Safety: this is safe because these page tables were fully initialised in the initial
    // bootstrap assembly.
    let pml4 = unsafe { PML4.assume_init_mut() };
    let pdpt = unsafe { PDPT.assume_init_mut() };
    let pd_0 = unsafe { PD_0.assume_init_mut() };
    let pd_3 = unsafe { PD_3.assume_init_mut() };
    let pt_0 = unsafe { PT_0.assume_init_mut() };

    let page_tables = PageTableRefs {
        pml4,
        pdpt,
        pd_0,
        pd_3,
        pt_0,
    };

    if PAGE_TABLE_REFS.set(Spinlock::new(page_tables)).is_err() {
        panic!("page table wrapper already initialized");
    }
}

/// Maps the first 1GiB of memory using 2MiB hugepages, except for the first 2MiB that was already
/// mapped as 512 4KiB pages in the bootstrap assembly.
pub fn map_additional_memory(encrypted: u64) {
    {
        let mut page_tables = PAGE_TABLE_REFS
            .get()
            .expect("page tables not initiallized")
            .lock();
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

// Remaps the first 2MiB of memory, which was mapped as 512 4KiB pages in the bootstrap assembly, as
// a single 2MiB huge page.
pub fn remap_first_huge_page(encrypted: u64) {
    {
        let mut page_tables = PAGE_TABLE_REFS
            .get()
            .expect("page tables not initiallized")
            .lock();
        let pd = &mut page_tables.pd_0;

        // Allow identity-op to keep the fact that the address we're talking about here is 0x00.
        #[allow(clippy::identity_op)]
        pd[0].set_addr(
            PhysAddr::new(0x0 | encrypted),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
        );
    }

    flush_all();
}
