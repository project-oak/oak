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

use crate::sev_status;
use oak_core::sync::OnceCell;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
pub use oak_sev_guest::ghcb::Ghcb;
use oak_sev_guest::{
    ghcb::GhcbProtocol,
    instructions::{pvalidate, InstructionError, PageSize as SevPageSize, Validation},
    msr::{
        change_snp_page_state, register_ghcb_location, PageAssignment, RegisterGhcbGpaRequest,
        SevStatus, SnpPageStateChangeRequest,
    },
};
use spinning_top::Spinlock;
use x86_64::{
    instructions::tlb,
    structures::paging::{
        frame::PhysFrameRange, page::AddressNotAligned, Page, PageSize, PageTable, PageTableFlags,
        PhysFrame, Size1GiB, Size2MiB, Size4KiB,
    },
    PhysAddr, VirtAddr,
};

pub static GHCB_WRAPPER: OnceCell<Spinlock<GhcbProtocol<'static, Ghcb>>> = OnceCell::new();

pub fn init_ghcb(ghcb: &'static mut Ghcb) {
    let ghcb_addr = VirtAddr::from_ptr(ghcb as *const _);

    share_page(Page::containing_address(ghcb_addr));

    // SNP requires that the GHCB is registered with the hypervisor.
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        let ghcb_location_request = RegisterGhcbGpaRequest::new(ghcb_addr.as_u64() as usize)
            .expect("invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("couldn't register the GHCB address with the hypervisor");
    }

    ghcb.reset();

    // We can't use `.expect()` here as Spinlock doesn't implement `fmt::Debug`.
    if GHCB_WRAPPER
        .set(Spinlock::new(GhcbProtocol::new(ghcb, |vaddr: VirtAddr| {
            Some(PhysAddr::new(vaddr.as_u64()))
        })))
        .is_err()
    {
        panic!("couldn't initialize GHCB wrapper");
    }
}

/// Stops sharing the GHCB with the hypervisor when running with AMD SEV-SNP enabled.
pub fn deinit_ghcb() {
    let ghcb_addr = VirtAddr::new(GHCB_WRAPPER.get().unwrap().lock().get_gpa().as_u64());
    unshare_page(Page::containing_address(ghcb_addr));
}

/// Shares a single 4KiB page with the hypervisor.
pub fn share_page(page: Page<Size4KiB>) {
    let page_start = page.start_address().as_u64();
    // Only the first 2MiB is mapped as 4KiB pages, so make sure we fall in that range.
    assert!(page_start < Size2MiB::SIZE);
    // Remove the ENCRYPTED bit from the entry that maps the page.
    {
        let mut page_tables = crate::paging::PAGE_TABLE_REFS.get().unwrap().lock();
        let pt = &mut page_tables.pt_0;
        let idx = (page_start / Size4KiB::SIZE) as usize;
        pt[idx].set_addr(
            PhysAddr::new(page_start),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
        );
    }
    tlb::flush_all();

    // SNP requires extra handling beyond just removing the encrypted bit.
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        let request = SnpPageStateChangeRequest::new(page_start as usize, PageAssignment::Shared)
            .expect("invalid address for page location");
        change_snp_page_state(request).expect("couldn't change SNP state for page");
    }
}

/// Stops sharing a single 4KiB page with the hypervisor when running with AMD SEV-SNP enabled.
pub fn unshare_page(page: Page<Size4KiB>) {
    let page_start = page.start_address().as_u64();
    let request = SnpPageStateChangeRequest::new(page_start as usize, PageAssignment::Private)
        .expect("invalid address for page location");
    change_snp_page_state(request).expect("couldn't change SNP state for page");
}

// Page tables come in three sizes: for 1 GiB, 2 MiB and 4 KiB pages. However, `PVALIDATE` can only
// be invoked on 2 MiB and 4 KiB pages.
// This trait translates between the page sizes defined in the x86_64 crate (`Size4KiB`, `Size2MiB`)
// and the sizes defined in `oak_sev_guest` crate (`Page4KiB`, `Page2MiB`). There is no mapping for
// `Size1GiB` as pages of that size can't be used for valitation.
pub trait ValidatablePageSize {
    const SEV_PAGE_SIZE: SevPageSize;
}

impl ValidatablePageSize for Size4KiB {
    const SEV_PAGE_SIZE: SevPageSize = SevPageSize::Page4KiB;
}

impl ValidatablePageSize for Size2MiB {
    const SEV_PAGE_SIZE: SevPageSize = SevPageSize::Page2MiB;
}

trait Validate<S: PageSize> {
    fn pvalidate(&self) -> Result<(), InstructionError>;
}

impl<S: PageSize + ValidatablePageSize> Validate<S> for Page<S> {
    fn pvalidate(&self) -> Result<(), InstructionError> {
        pvalidate(
            self.start_address().as_u64() as usize,
            S::SEV_PAGE_SIZE,
            Validation::Validated,
        )
    }
}

/// Container for a page of virtual memory, and the page table that controls the mappings for that
/// page.
struct MappedPage<S: PageSize> {
    pub page: Page<S>,
    pub page_table: PageTable,
}

impl<S: PageSize> MappedPage<S> {
    pub fn new(vaddr: VirtAddr) -> Result<Self, AddressNotAligned> {
        let mapped_page = Self {
            page: Page::from_start_address(vaddr)?,
            page_table: PageTable::new(),
        };
        Ok(mapped_page)
    }
}

fn pvalidate_range<S: PageSize + ValidatablePageSize, T: PageSize, F>(
    range: &PhysFrameRange<S>,
    memory: &mut MappedPage<T>,
    encrypted: u64,
    flags: PageTableFlags,
    mut f: F,
) -> Result<(), InstructionError>
where
    F: FnMut(PhysAddr, InstructionError) -> Result<(), InstructionError>,
{
    // Create a copy as we'll be consuming the range as we call `next()`, below.
    let mut range = *range;

    // A page table consists of 512 entries; let's figure out what the pages would be.
    let start = Page::from_start_address(memory.page.start_address()).unwrap();
    let pages = Page::<S>::range(start, start + 512);

    // We have 512 entries to play with, but the frame range can contain many more entries than
    // that. Thus, we need to iterate over the range in chunks of 512; the easiest way to do it is
    // to iterate (mutably) over the page directory itself, and for each entry, fetch the next
    // entry in the range. If we've covered everything, `range.next()` will return `None`, and
    // the count will be zero once we've covered everything.
    memory.page_table.zero();
    while memory
        .page_table
        .iter_mut()
        .filter_map(|entry| range.next().map(|frame| (entry, frame)))
        .map(|(entry, frame)| {
            entry.set_addr(
                frame.start_address() + encrypted,
                PageTableFlags::PRESENT | flags,
            )
        })
        .count()
        > 0
    {
        // We now know we've filled in at least one entry of the page table, and thus have something
        // to validate.
        tlb::flush_all();

        if let Some(err) = memory
            .page_table
            .iter()
            .zip(pages)
            .filter(|(entry, _)| !entry.is_unused())
            .map(|(entry, page)| (entry, page.pvalidate()))
            .map(|(entry, result)| result.or_else(|err| f(entry.addr(), err)))
            .find(|result| result.is_err())
        {
            return err;
        }

        // Clear out the page table, ready for the next iteration.
        memory.page_table.zero();
    }

    Ok(())
}

trait Validatable4KiB {
    /// Validate a region of memory using 4 KiB pages.
    ///
    /// Args:
    ///   pt: pointer to the page table we can mutate to map 4 KiB pages to memory
    ///   encrypted: value of the encrypted bit in the page table
    fn pvalidate(
        &self,
        pt: &mut MappedPage<Size2MiB>,
        encrypted: u64,
    ) -> Result<(), InstructionError>;
}

impl Validatable4KiB for PhysFrameRange<Size4KiB> {
    fn pvalidate(
        &self,
        pt: &mut MappedPage<Size2MiB>,
        encrypted: u64,
    ) -> Result<(), InstructionError> {
        pvalidate_range(
            self,
            pt,
            encrypted,
            PageTableFlags::empty(),
            |_addr, err| match err {
                InstructionError::ValidationStatusNotUpdated => {
                    // We don't treat this as an error. It only happens if SEV-SNP is not enabled,
                    // or it is already validated. See the PVALIDATE instruction in
                    // <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
                    Ok(())
                }
                other => Err(other),
            },
        )
    }
}

trait Validatable2MiB {
    /// Validate a region of memory using 2 MiB pages, falling back to 4 KiB if necessary.
    ///
    /// Args:
    ///   pd: pointer to the page directory we can mutate to map 2 MiB pages to memory
    ///   pt: pointer to the page table we can mutate to map 4 KiB pages to memory
    ///   encrypted: value of the encrypted bit in the page table
    fn pvalidate(
        &self,
        pd: &mut MappedPage<Size1GiB>,
        pt: &mut MappedPage<Size2MiB>,
        encrypted: u64,
    ) -> Result<(), InstructionError>;
}

impl Validatable2MiB for PhysFrameRange<Size2MiB> {
    fn pvalidate(
        &self,
        pd: &mut MappedPage<Size1GiB>,
        pt: &mut MappedPage<Size2MiB>,
        encrypted: u64,
    ) -> Result<(), InstructionError> {
        pvalidate_range(
            self,
            pd,
            encrypted,
            PageTableFlags::HUGE_PAGE,
            |addr, err| match err {
                InstructionError::FailSizeMismatch => {
                    // 2MiB is no go, fail back to 4KiB pages.
                    // This will not panic as every address that is 2 MiB-aligned is by definition
                    // also 4 KiB-aligned.
                    let start = PhysFrame::<Size4KiB>::from_start_address(PhysAddr::new(
                        addr.as_u64() & !encrypted,
                    ))
                    .unwrap();
                    let range = PhysFrame::range(start, start + 512);
                    range.pvalidate(pt, encrypted)
                }
                InstructionError::ValidationStatusNotUpdated => {
                    // We don't treat this as an error. It only happens if SEV-SNP is not enabled,
                    // or it is already validated. See the PVALIDATE instruction in
                    // <https://www.amd.com/system/files/TechDocs/24594.pdf> for more details.
                    Ok(())
                }
                other => Err(other),
            },
        )
    }
}

/// Calls `PVALIDATE` on all memory ranges specified in the E820 table with type `RAM`.
pub fn validate_memory(e820_table: &[BootE820Entry], encrypted: u64) {
    log::info!("starting SEV-SNP memory validation");

    let mut page_tables = crate::paging::PAGE_TABLE_REFS.get().unwrap().lock();

    // Page directory, for validation with 2 MiB pages.
    let mut validation_pd = MappedPage::new(VirtAddr::new(Size1GiB::SIZE)).unwrap();
    // For virtual address space, we currently shouldn't have anything at the second gigabyte, so we
    // can map the page to virtual address [1 GiB..2 GiB).
    if page_tables.pdpt[1]
        .flags()
        .contains(PageTableFlags::PRESENT)
    {
        panic!("PDPT[1] is in use");
    }
    page_tables.pdpt[1].set_addr(
        PhysAddr::new(&validation_pd.page_table as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT,
    );

    // Page table, for validation with 4 KiB pages.
    let mut validation_pt = MappedPage::new(VirtAddr::new(Size2MiB::SIZE)).unwrap();
    // Find a location for our (temporary) page table. The initial page tables map [0..2MiB), so it
    // should be safe to put our temporary mappings at [2..4MiB).
    if page_tables.pd_0[1]
        .flags()
        .contains(PageTableFlags::PRESENT)
    {
        panic!("PD_0[1] is in use");
    }
    page_tables.pd_0[1].set_addr(
        PhysAddr::new(&validation_pt.page_table as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT,
    );

    // We already pvalidated the memory in the first 640KiB of RAM in the boot assembly code. We
    // avoid redoing this as calling pvalidate again on these pages leads to unexpected results,
    // such us removing the shared state from the RMP for the fw_cfg DMA buffer.
    let min_addr = 0xA0000;

    for entry in e820_table {
        if entry.entry_type() != Some(E820EntryType::RAM) || entry.addr() < min_addr {
            continue;
        }

        let start_address = PhysAddr::new(entry.addr() as u64);
        let limit_address = PhysAddr::new((entry.addr() + entry.size()) as u64);

        // If the memory boundaries align with 2 MiB, start with that.
        if start_address.is_aligned(Size2MiB::SIZE) && limit_address.is_aligned(Size2MiB::SIZE) {
            // These unwraps can't fail as we've made sure that the addresses are 2 MiB-aligned.
            let range = PhysFrame::<Size2MiB>::range(
                PhysFrame::from_start_address(start_address).unwrap(),
                PhysFrame::from_start_address(limit_address).unwrap(),
            );
            range.pvalidate(&mut validation_pd, &mut validation_pt, encrypted)
        } else {
            // No such luck, fail over to 4K pages.
            // The unwraps can't fail as we make sure that the addresses are 4 KiB-aligned.
            let range = PhysFrame::<Size4KiB>::range(
                PhysFrame::from_start_address(start_address.align_up(Size4KiB::SIZE)).unwrap(),
                PhysFrame::from_start_address(limit_address.align_down(Size4KiB::SIZE)).unwrap(),
            );
            range.pvalidate(&mut validation_pt, encrypted)
        }
        .expect("failed to validate memory");
    }
    page_tables.pd_0[1].set_unused();
    page_tables.pdpt[1].set_unused();
    tlb::flush_all();
    log::info!("SEV-SNP memory validation complete.");
}
