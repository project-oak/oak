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
use core::{
    ops::{Index, IndexMut},
    ptr::addr_of_mut,
};

use oak_core::sync::OnceCell;
use spinning_top::Spinlock;
use x86_64::{
    instructions::tlb::flush_all,
    structures::paging::{
        page_table::{PageTableEntry as BasePageTableEntry, PageTableFlags},
        Page, PageSize, PageTable as BasePageTable, PageTableIndex, Size2MiB, Size4KiB,
    },
    PhysAddr,
};

use crate::{hal::PageAssignment, BootAllocator, Platform, BOOT_ALLOC};

pub static mut PML4: PageTable = PageTable::new();
pub static mut PDPT: PageTable = PageTable::new();
pub static mut PD_0: PageTable = PageTable::new();
pub static mut PD_3: PageTable = PageTable::new();

/// Wrapper for the page table references so that we can access them via a mutex
/// rather than directly via unsafe code.
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
    pub pt_0: Box<PageTable, &'static BootAllocator>,
}

/// References to all the pages tables we care about.
pub static PAGE_TABLE_REFS: OnceCell<Spinlock<PageTableRefs>> = OnceCell::new();

/// Thin wrapper around x86::PageTable that uses our PageTableEntry type.
#[repr(transparent)]
pub struct PageTable(BasePageTable);

impl PageTable {
    pub const fn new() -> Self {
        Self(BasePageTable::new())
    }

    pub fn zero(&mut self) {
        self.0.zero()
    }

    pub fn iter(&self) -> impl Iterator<Item = &PageTableEntry> {
        self.0.iter().map(|entry| entry.into())
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PageTableEntry> {
        self.0.iter_mut().map(|entry| entry.into())
    }
}

impl Index<usize> for PageTable {
    type Output = PageTableEntry;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index).into()
    }
}

impl Index<PageTableIndex> for PageTable {
    type Output = PageTableEntry;

    fn index(&self, index: PageTableIndex) -> &Self::Output {
        self.0.index(index).into()
    }
}

impl IndexMut<usize> for PageTable {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.0.index_mut(index).into()
    }
}

impl IndexMut<PageTableIndex> for PageTable {
    fn index_mut(&mut self, index: PageTableIndex) -> &mut Self::Output {
        self.0.index_mut(index).into()
    }
}

/// Thin wrapper around x86_64::PageTableEntry that forces use of PageEncryption
/// for addresses.
#[repr(transparent)]
#[derive(Clone)]
pub struct PageTableEntry(BasePageTableEntry);

impl PageTableEntry {
    /// Map the entry to the specified address with the specified flags and
    /// encryption state.
    pub fn set_address<P: Platform>(
        &mut self,
        addr: PhysAddr,
        flags: PageTableFlags,
        state: PageEncryption,
    ) {
        let addr = PhysAddr::new(addr.as_u64() | P::page_table_mask(state));
        self.0.set_addr(addr, flags);
    }

    /// Returns the physical address mapped by this entry. May be zero.
    pub fn address<P: Platform>(&self) -> PhysAddr {
        PhysAddr::new(self.0.addr().as_u64() & !P::encrypted())
    }

    /// Returns whether the entry is zero.
    pub const fn is_unused(&self) -> bool {
        self.0.is_unused()
    }

    /// Sets the entry to zero.
    pub fn set_unused(&mut self) {
        self.0.set_unused()
    }

    /// Returns the flags of this entry.
    pub const fn flags(&self) -> PageTableFlags {
        self.0.flags()
    }
}

impl From<&BasePageTableEntry> for &PageTableEntry {
    fn from(value: &BasePageTableEntry) -> Self {
        // Safety: our PageTableEntry is a transparent wrapper so the memory layout is
        // the same and does not impose any extra restrictions on valid values.
        unsafe { &*(value as *const BasePageTableEntry as *const PageTableEntry) }
    }
}

impl From<&mut BasePageTableEntry> for &mut PageTableEntry {
    fn from(value: &mut BasePageTableEntry) -> Self {
        // Safety: our PageTableEntry is a transparent wrapper so the memory layout is
        // the same and does not impose any extra restrictions on valid values.
        unsafe { &mut *(value as *mut BasePageTableEntry as *mut PageTableEntry) }
    }
}

/// Encryption state of a page in the page table.
pub enum PageEncryption {
    Encrypted,
    Unencrypted,
}

/// Initialises the page table references.
pub fn init_page_table_refs<P: Platform>() {
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
    let mut pt_0 = Box::new_in(PageTable::new(), &BOOT_ALLOC);
    pt_0.iter_mut().enumerate().skip(1).for_each(|(i, entry)| {
        entry.set_address::<P>(
            PhysAddr::new((i as u64) * Size4KiB::SIZE),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
            PageEncryption::Encrypted,
        );
    });
    pd_0[0].set_address::<P>(
        PhysAddr::new(pt_0.as_ref() as *const _ as usize as u64),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
        PageEncryption::Encrypted,
    );

    let page_tables = PageTableRefs { pml4, pdpt, pd_0, pd_3, pt_0 };

    if PAGE_TABLE_REFS.set(Spinlock::new(page_tables)).is_err() {
        panic!("page table wrapper already initialized");
    }

    flush_all();
}

/// Maps the first 1GiB of memory using 2MiB hugepages, except for the first
/// 2MiB that was already mapped as 512 4KiB pages.
pub fn map_additional_memory<P: Platform>() {
    {
        let mut page_tables = PAGE_TABLE_REFS.get().expect("page tables not initiallized").lock();
        let pd = &mut page_tables.pd_0;
        pd.iter_mut().enumerate().skip(1).for_each(|(i, entry)| {
            entry.set_address::<P>(
                PhysAddr::new((i as u64) * Size2MiB::SIZE),
                PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
                PageEncryption::Encrypted,
            );
        });
    }

    flush_all();
}

// Remaps the first 2MiB of memory, which was previously mapped as 512 4KiB
// pages, as a single 2MiB huge page again.
pub fn remap_first_huge_page<P: Platform>() {
    {
        let mut page_tables = PAGE_TABLE_REFS.get().expect("page tables not initiallized").lock();
        let pd = &mut page_tables.pd_0;

        pd[0].set_address::<P>(
            PhysAddr::new(0x0),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
            PageEncryption::Encrypted,
        );
    }

    flush_all();
}

/// Shares a single 4KiB page with the hypervisor.
pub fn share_page<P: Platform>(page: Page<Size4KiB>) {
    let page_start = page.start_address().as_u64();
    // Only the first 2MiB is mapped as 4KiB pages, so make sure we fall in that
    // range.
    assert!(page_start < Size2MiB::SIZE);
    // Remove the ENCRYPTED bit from the entry that maps the page.
    {
        let mut page_tables = crate::paging::PAGE_TABLE_REFS.get().unwrap().lock();
        let pt = &mut page_tables.pt_0;
        pt[page.p1_index()].set_address::<P>(
            PhysAddr::new(page_start),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
            PageEncryption::Unencrypted,
        );
    }
    flush_all();

    P::change_page_state(page, PageAssignment::Shared);
}

/// Stops sharing a single 4KiB page with the hypervisor when running with AMD
/// SEV-SNP enabled.
pub fn unshare_page<P: Platform>(page: Page<Size4KiB>) {
    let page_start = page.start_address().as_u64();
    // Only the first 2MiB is mapped as 4KiB pages, so make sure we fall in that
    // range.
    assert!(page_start < Size2MiB::SIZE);
    P::change_page_state(page, PageAssignment::Private);
    // Mark the page as encrypted.
    {
        let mut page_tables = crate::paging::PAGE_TABLE_REFS.get().unwrap().lock();
        let pt = &mut page_tables.pt_0;
        pt[page.p1_index()].set_address::<P>(
            PhysAddr::new(page_start),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
            PageEncryption::Encrypted,
        );
    }
    flush_all();

    // We have to revalidate the page again after un-sharing it.
    P::revalidate_page(page);
}
