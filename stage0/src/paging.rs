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
    marker::PhantomData,
    ops::{Index, IndexMut},
    pin::Pin,
    ptr::addr_of_mut,
};

use oak_core::sync::OnceCell;
use spinning_top::Spinlock;
use x86_64::{
    PhysAddr,
    instructions::tlb::flush_all,
    structures::paging::{
        Page, PageSize, PageTable as BasePageTable, PageTableIndex, Size2MiB, Size4KiB,
        page_table::{PageTableEntry as BasePageTableEntry, PageTableFlags},
    },
};

use crate::{BOOT_ALLOC, BootAllocator, Platform, hal::PageAssignment};

/// The root page-map level 4 table coverting virtual memory ranges 0..128TiB
/// and (16EiB-128TiB)..16EiB.
pub static mut PML4: PageTable<page_table_level::PML4> = PageTable::new();
/// The page-directory pointer table covering virtual memory range 0..512GiB.
pub static mut PDPT: PageTable<page_table_level::PDPT> = PageTable::new();
/// The page directory covering virtual memory range 0..1GiB.
pub static mut PD_0: PageTable<page_table_level::PD> = PageTable::new();
/// The page directory covering virtual memory range 3..4GiB.
pub static mut PD_3: PageTable<page_table_level::PD> = PageTable::new();

/// Wrapper for the page table references so that we can access them via a mutex
/// rather than directly via unsafe code.
pub struct PageTableRefs {
    /// The root page-map level 4 table coverting virtual memory ranges
    /// 0..128TiB and (16EiB-128TiB)..16EiB.
    pub pml4: Pin<&'static mut PageTable<page_table_level::PML4>>,

    /// The page-directory pointer table covering virtual memory range
    /// 0..512GiB.
    pub pdpt: Pin<&'static mut PageTable<page_table_level::PDPT>>,

    /// The page directory covering virtual memory range 0..1GiB.
    pub pd_0: Pin<&'static mut PageTable<page_table_level::PD>>,

    /// The page directory covering virtual memory range 3..4GiB.
    pub pd_3: Pin<&'static mut PageTable<page_table_level::PD>>,

    /// The page table covering virtual memory range 0..2MiB where we want 4KiB
    /// pages.
    pub pt_0: Pin<Box<PageTable<page_table_level::PT>, &'static BootAllocator>>,
}

/// References to all the pages tables we care about.
pub static PAGE_TABLE_REFS: OnceCell<Spinlock<PageTableRefs>> = OnceCell::new();

pub mod page_table_level {
    use x86_64::structures::paging::{PageSize, PageTableFlags, Size1GiB, Size2MiB, Size4KiB};

    pub trait PageTableLevel {}

    /// Marker trait for page tables that may have nested page tables.
    pub trait Node: PageTableLevel {
        /// Type of the lower level of page tables in the hierarchy.
        type Nested: PageTableLevel;
    }

    /// Marker trait for page tables that can map memory.
    pub trait Leaf: PageTableLevel {
        /// Flags to be used (e.g. HUGE_PAGE for non-4K pages)
        const FLAGS: PageTableFlags;

        /// Size of the page.
        type Size: PageSize;
    }

    /// Page Map Level 4
    #[derive(Clone)]
    pub enum PML4 {}
    impl PageTableLevel for PML4 {}
    impl Node for PML4 {
        type Nested = PDPT;
    }

    /// Page Directory Pointer Table (Level 3)
    #[derive(Clone)]
    pub enum PDPT {}
    impl PageTableLevel for PDPT {}
    impl Node for PDPT {
        type Nested = PD;
    }
    impl Leaf for PDPT {
        const FLAGS: PageTableFlags = PageTableFlags::HUGE_PAGE;
        type Size = Size1GiB;
    }

    /// Page Directory (Level 2)
    #[derive(Clone)]
    pub enum PD {}
    impl PageTableLevel for PD {}
    impl Node for PD {
        type Nested = PT;
    }
    impl Leaf for PD {
        const FLAGS: PageTableFlags = PageTableFlags::HUGE_PAGE;
        type Size = Size2MiB;
    }

    /// Page Table (Level 1)
    #[derive(Clone)]
    pub enum PT {}
    impl PageTableLevel for PT {}
    impl Leaf for PT {
        const FLAGS: PageTableFlags = PageTableFlags::empty();
        type Size = Size4KiB;
    }
}
pub use page_table_level::{Leaf, PageTableLevel};

/// Thin wrapper around x86::PageTable that uses our PageTableEntry type.
#[repr(transparent)]
#[derive(Default)]
pub struct PageTable<PageTableLevel> {
    inner: BasePageTable,
    phantom: PhantomData<PageTableLevel>,
}

impl<L: PageTableLevel> PageTable<L> {
    pub const fn new() -> Self {
        Self { inner: BasePageTable::new(), phantom: PhantomData }
    }

    pub fn zero(&mut self) {
        self.inner.zero()
    }

    pub fn iter(&self) -> impl Iterator<Item = &PageTableEntry<L>> {
        self.inner.iter().map(|entry| entry.into())
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PageTableEntry<L>> {
        self.inner.iter_mut().map(|entry| entry.into())
    }
}

impl<L: PageTableLevel> Index<usize> for PageTable<L> {
    type Output = PageTableEntry<L>;

    fn index(&self, index: usize) -> &Self::Output {
        self.inner.index(index).into()
    }
}

impl<L: PageTableLevel> Index<PageTableIndex> for PageTable<L> {
    type Output = PageTableEntry<L>;

    fn index(&self, index: PageTableIndex) -> &Self::Output {
        self.inner.index(index).into()
    }
}

impl<L: PageTableLevel> IndexMut<usize> for PageTable<L> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.inner.index_mut(index).into()
    }
}

impl<L: PageTableLevel> IndexMut<PageTableIndex> for PageTable<L> {
    fn index_mut(&mut self, index: PageTableIndex) -> &mut Self::Output {
        self.inner.index_mut(index).into()
    }
}

/// Thin wrapper around x86_64::PageTableEntry that forces use of PageEncryption
/// for addresses.
#[repr(transparent)]
#[derive(Clone)]
pub struct PageTableEntry<PageTableLevel> {
    inner: BasePageTableEntry,
    phantom: PhantomData<PageTableLevel>,
}

impl<L: page_table_level::PageTableLevel, Ln: page_table_level::PageTableLevel> PageTableEntry<L>
where
    L: page_table_level::Node<Nested = Ln>,
{
    /// Sets the entry to point to a lower level page table with the specified
    /// flags.
    ///
    /// Encryption bit is never set, as this is not required for neither SEV nor
    /// TDX.
    pub fn set_lower_level_table<P: Platform>(
        &mut self,
        pt: Pin<&PageTable<Ln>>,
        flags: PageTableFlags,
    ) {
        self.inner.set_addr(PhysAddr::new(pt.get_ref() as *const _ as u64), flags)
    }
}

impl<L: PageTableLevel + Leaf> PageTableEntry<L> {
    /// Map the entry to the specified address in memory with the specified
    /// flags and encryption state.
    ///
    /// You don't need to set the HUGE_PAGE flag; it will be added
    /// automatically.
    ///
    /// Don't use this to set up nested page tables!
    pub fn set_address<P: Platform>(
        &mut self,
        addr: PhysAddr,
        flags: PageTableFlags,
        state: PageEncryption,
    ) {
        let addr = PhysAddr::new(addr.as_u64() | P::page_table_mask(state));
        self.inner.set_addr(addr, flags | L::FLAGS);
    }
}

impl<L: PageTableLevel> PageTableEntry<L> {
    /// Returns the physical address mapped by this entry. May be zero.
    pub fn address<P: Platform>(&self) -> PhysAddr {
        PhysAddr::new(self.inner.addr().as_u64() & !P::encrypted())
    }

    /// Returns whether the entry is zero.
    pub const fn is_unused(&self) -> bool {
        self.inner.is_unused()
    }

    /// Sets the entry to zero.
    pub fn set_unused(&mut self) {
        self.inner.set_unused()
    }

    /// Returns the flags of this entry.
    pub const fn flags(&self) -> PageTableFlags {
        self.inner.flags()
    }
}

impl<L: PageTableLevel> From<&BasePageTableEntry> for &PageTableEntry<L> {
    fn from(value: &BasePageTableEntry) -> Self {
        // Safety: our PageTableEntry is a transparent wrapper so the memory layout is
        // the same and does not impose any extra restrictions on valid values.
        unsafe { &*(value as *const BasePageTableEntry as *const PageTableEntry<L>) }
    }
}

impl<L: PageTableLevel> From<&mut BasePageTableEntry> for &mut PageTableEntry<L> {
    fn from(value: &mut BasePageTableEntry) -> Self {
        // Safety: our PageTableEntry is a transparent wrapper so the memory layout is
        // the same and does not impose any extra restrictions on valid values.
        unsafe { &mut *(value as *mut BasePageTableEntry as *mut PageTableEntry<L>) }
    }
}

/// Encryption state of a page in the page table.
///
/// Setting the encrypted bit makes only sense for a leaf page table.
///
/// For AMD SEV, see Section 15.34.5, SEV Encryption Behavior:
/// > When a guest is executed with SEV enabled, the guest page tables are used
/// > to determine the C-bit for a memory page and hence the encryption status
/// > of that memory page. This allows a guest to determine which pages are
/// > private or shared, but this control is available only for data pages.
/// > Memory accesses on behalf of instruction fetches and guest page table
/// > walks are always treated as private, regardless of the software value of
/// > the C-bit.
///
/// As the memory accesses for page table walks are always treated as private,
/// it doesn't matter whether we set the C-bit on non-leaf entries.
///
/// For Intel TDX, the `Encrypted` == `Unset``, so it's safe to use `Unset` for
/// TDX page tables as well.
pub enum PageEncryption {
    /// Always defaults to "don't set the encrypted bit", no matter its
    /// semantics. This should be the default for non-leaf page table
    /// entries.
    Unset,

    /// Ensures that the encrypted bit is enabled.
    Encrypted,

    /// Ensures that the encrypted bit is disabled.
    Unencrypted,
}

/// Initialises the page table references.
pub fn init_page_table_refs<P: Platform>() {
    // Safety: accessing the mutable statics here is safe since we only do it once
    // and protect the mutable references with a mutex. This function can only
    // be called once, since updating `PAGE_TABLE_REFS` twice will panic.
    let pml4 = Pin::static_mut(unsafe { &mut *addr_of_mut!(PML4) });
    let pdpt = Pin::static_mut(unsafe { &mut *addr_of_mut!(PDPT) });
    let mut pd_0 = Pin::static_mut(unsafe { &mut *addr_of_mut!(PD_0) });
    let pd_3 = Pin::static_mut(unsafe { &mut *addr_of_mut!(PD_3) });

    // Set up a new page table that maps the first 2MiB as 4KiB pages (except for
    // the lower 4KiB), so that we can share individual 4KiB pages with the
    // hypervisor as needed. We are using an identity mapping between virtual
    // and physical addresses.
    let mut pt_0 = Box::pin_in(PageTable::new(), &BOOT_ALLOC);
    // Let entry 1 map to 4KiB, entry 2 to 8KiB, ... , entry 511 to 2MiB-4KiB:
    // We leave [0,4K) unmapped to make sure null pointer dereferences crash
    // with a page fault.
    pt_0.iter_mut().enumerate().skip(1).for_each(|(i, entry)| {
        entry.set_address::<P>(
            PhysAddr::new((i as u64) * Size4KiB::SIZE),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
            PageEncryption::Encrypted,
        );
    });
    // Let the first entry of PD_0 point to pt_0:
    pd_0[0].set_lower_level_table::<P>(
        pt_0.as_ref(),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );

    let page_tables = PageTableRefs { pml4, pdpt, pd_0, pd_3, pt_0 };

    if PAGE_TABLE_REFS.set(Spinlock::new(page_tables)).is_err() {
        panic!("page table wrapper already initialized");
    }

    flush_all();
}

/// Identity maps the first 1GiB of memory using 2MiB hugepages, except for the
/// first 2MiB that was already mapped as 512 4KiB pages.
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
