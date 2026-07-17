//
// Copyright 2024 The Project Oak Authors
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

use alloc::boxed::Box;
use core::{
    pin::Pin,
    sync::atomic::{AtomicUsize, Ordering},
};

use oak_hal::PageAssignment;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use oak_sev_guest::{
    instructions::{InstructionError, PageSize as SevPageSize, Validation, pvalidate},
    msr::{
        PageAssignment as MsrPageAssignment, SevStatus, SnpPageStateChangeRequest,
        change_snp_page_state,
    },
};
use oak_stage0::paging::{
    PageTable,
    page_table_level::{Leaf, PD, PT},
};
use x86_64::{
    PhysAddr, VirtAddr,
    instructions::tlb,
    structures::paging::{
        Page, PageSize, PageTableFlags, PhysFrame, Size1GiB, Size2MiB, Size4KiB,
        frame::PhysFrameRange,
        page::{AddressNotAligned, NotGiantPageSize},
    },
};
use zeroize::Zeroize;

use crate::platform::{GHCB_WRAPPER, IntoMsrPageAssignment, Sev, sev_status};

//
// Page tables come in three sizes: for 1 GiB, 2 MiB and 4 KiB pages. However,
// `PVALIDATE` can only be invoked on 2 MiB and 4 KiB pages.
// This trait translates between the page sizes defined in the x86_64 crate
// (`Size4KiB`, `Size2MiB`) and the sizes defined in `oak_sev_guest` crate
// (`Page4KiB`, `Page2MiB`). There is no mapping for `Size1GiB` as pages of that
// size can't be used for valitation.
trait ValidatablePageSize {
    const SEV_PAGE_SIZE: SevPageSize;
}

impl ValidatablePageSize for Size4KiB {
    const SEV_PAGE_SIZE: SevPageSize = SevPageSize::Page4KiB;
}

impl ValidatablePageSize for Size2MiB {
    const SEV_PAGE_SIZE: SevPageSize = SevPageSize::Page2MiB;
}

trait Validate<S: PageSize> {
    fn pvalidate(&self, counter: &AtomicUsize) -> Result<(), InstructionError>;
}

impl<S: PageSize + ValidatablePageSize> Validate<S> for Page<S> {
    fn pvalidate(&self, counter: &AtomicUsize) -> Result<(), InstructionError> {
        pvalidate(self.start_address().as_u64() as usize, S::SEV_PAGE_SIZE, Validation::Validated)?;
        let start = Page::from_start_address(self.start_address()).unwrap();
        let end = Page::from_start_address(VirtAddr::new(self.start_address().as_u64() + S::SIZE))
            .unwrap();
        // non-inclusive end
        let range = Page::<Size4KiB>::range(start, end);

        // Read the first and last byte of each 4K page validated to evict cache
        // (CVE-2025-38560)
        range.for_each(|page| {
            let _val = unsafe { page.start_address().as_ptr::<u8>().read_volatile() };
            // Due to the nature of CVE-2025-38560, we have to force a flush
            // for each 4K page even if these are huge pages
            let _val2 = unsafe {
                page.start_address().as_ptr::<u8>().add(Size4KiB::SIZE as usize - 1).read_volatile()
            };
        });

        counter.fetch_add(1, Ordering::SeqCst);
        Ok(())
    }
}

/// Container for a page of virtual memory, and the page table that controls the
/// mappings for that page.
struct MappedPage<L: Leaf> {
    pub page: Page<L::Size>,
    pub page_table: Pin<Box<PageTable<L>, &'static oak_stage0::BootAllocator>>,
}

impl<L: Leaf> MappedPage<L> {
    pub fn new(vaddr: VirtAddr) -> Result<Self, AddressNotAligned> {
        let mapped_page = Self {
            page: Page::from_start_address(vaddr)?,
            page_table: Box::pin_in(PageTable::new(), &oak_stage0::BOOT_ALLOC),
        };
        Ok(mapped_page)
    }
}

fn pvalidate_range<S: NotGiantPageSize + ValidatablePageSize, L: Leaf, F>(
    range: &PhysFrameRange<S>,
    memory: &mut MappedPage<L>,
    flags: PageTableFlags,
    success_counter: &AtomicUsize,
    mut f: F,
) -> Result<(), InstructionError>
where
    F: FnMut(PhysAddr, InstructionError) -> Result<(), InstructionError>,
{
    // Create a copy as we'll be consuming the range as we call `next()`, below.
    let mut range = *range;

    // A page table consists of 512 entries; let's figure out what the pages would
    // be.
    let start = Page::from_start_address(memory.page.start_address()).unwrap();
    let pages = Page::<S>::range(start, start + 512);

    // We have 512 entries to play with, but the frame range can contain many more
    // entries than that. Thus, we need to iterate over the range in chunks of
    // 512; the easiest way to do it is to iterate (mutably) over the page
    // directory itself, and for each entry, fetch the next entry in the range.
    // If we've covered everything, `range.next()` will return `None`, and
    // the count will be zero once we've covered everything.
    memory.page_table.set(PageTable::new());

    // Safety: the call to `get_unchecked_mut` is safe as we will _not_ move the
    // value out of `Pin`.
    while unsafe { memory.page_table.as_mut().get_unchecked_mut() }
        .iter_mut()
        .filter_map(|entry| range.next().map(|frame| (entry, frame)))
        .map(|(entry, frame)| {
            entry.set_address::<Sev>(
                frame.start_address(),
                PageTableFlags::PRESENT | flags,
                PageAssignment::Private,
            )
        })
        .count()
        > 0
    {
        // We now know we've filled in at least one entry of the page table, and thus
        // have something to validate.
        tlb::flush_all();

        if let Some(err) = memory
            .page_table
            .iter()
            .zip(pages)
            .filter(|(entry, _)| !entry.is_unused())
            .map(|(entry, page)| (entry, page.pvalidate(success_counter)))
            .map(|(entry, result)| result.or_else(|err| f(entry.address::<Sev>(), err)))
            .find(|result| result.is_err())
        {
            return err;
        }

        // Clear out the page table, ready for the next iteration.
        memory.page_table.set(PageTable::new());
    }

    Ok(())
}

mod counters {
    use core::sync::atomic::AtomicUsize;

    /// Number of PVALIDATE invocations that did not change Validated state.
    pub static ERROR_VALIDATION_STATUS_NOT_UPDATED: AtomicUsize = AtomicUsize::new(0);

    /// Number of FAIL_SIZEMISMATCH errors when invoking PVALIDATE on 2 MiB
    /// pages.
    pub static ERROR_FAIL_SIZE_MISMATCH: AtomicUsize = AtomicUsize::new(0);

    /// Number of successful PVALIDATE invocations on 2 MiB pages.
    pub static VALIDATED_2M: AtomicUsize = AtomicUsize::new(0);

    /// Number of successful PVALIDATE invocations on 4 KiB pages.
    pub static VALIDATED_4K: AtomicUsize = AtomicUsize::new(0);
}

trait Validatable4KiB {
    /// Validate a region of memory using 4 KiB pages.
    ///
    /// Args:
    ///   pt: pointer to the page table we can mutate to map 4 KiB pages to
    ///       memory
    fn pvalidate(&self, pt: &mut MappedPage<PT>) -> Result<(), InstructionError>;
}

impl Validatable4KiB for PhysFrameRange<Size4KiB> {
    fn pvalidate(&self, pt: &mut MappedPage<PT>) -> Result<(), InstructionError> {
        pvalidate_range(self, pt, PageTableFlags::empty(), &counters::VALIDATED_4K, |addr, err| {
            match err {
                InstructionError::ValidationStatusNotUpdated => {
                    // SECURITY: CF=1 during first-touch acceptance means the RMP entry for
                    // this GPA was already Validated=1. Under SNP this indicates a
                    // double-validation / page-aliasing attack by the hypervisor (the
                    // hypervisor can RMPUPDATE a second SPA to the same GPA and have us
                    // PVALIDATE it). AMD 56421 and the Linux/OVMF reference
                    // implementations require this to be fatal.
                    panic!(
                        "PVALIDATE CF=1 (double-validation) at GPA {:#x}; possible \
                         hypervisor page-aliasing attack",
                        addr.as_u64()
                    );
                }
                other => Err(other),
            }
        })
    }
}

trait Validatable2MiB {
    /// Validate a region of memory using 2 MiB pages, falling back to 4 KiB if
    /// necessary.
    ///
    /// Args:
    ///   pd: pointer to the page directory we can mutate to map 2 MiB pages to
    /// memory   pt: pointer to the page table we can mutate to map 4 KiB
    /// pages to memory   encrypted: value of the encrypted bit in the page
    /// table
    fn pvalidate(
        &self,
        pd: &mut MappedPage<PD>,
        pt: &mut MappedPage<PT>,
    ) -> Result<(), InstructionError>;
}

impl Validatable2MiB for PhysFrameRange<Size2MiB> {
    fn pvalidate(
        &self,
        pd: &mut MappedPage<PD>,
        pt: &mut MappedPage<PT>,
    ) -> Result<(), InstructionError> {
        pvalidate_range(
            self,
            pd,
            PageTableFlags::HUGE_PAGE,
            &counters::VALIDATED_2M,
            |addr, err| match err {
                InstructionError::FailSizeMismatch => {
                    // 2MiB is no go, fail back to 4KiB pages.
                    counters::ERROR_FAIL_SIZE_MISMATCH.fetch_add(1, Ordering::SeqCst);
                    // This will not panic as every address that is 2 MiB-aligned is by definition
                    // also 4 KiB-aligned.
                    let start = PhysFrame::<Size4KiB>::from_start_address(addr).unwrap();
                    let range = PhysFrame::range(start, start + 512);
                    range.pvalidate(pt)
                }
                InstructionError::ValidationStatusNotUpdated => {
                    // SECURITY: CF=1 during first-touch acceptance indicates a
                    // double-validation / page-aliasing attack by the hypervisor. See the
                    // 4 KiB path above for details. This must be fatal.
                    panic!(
                        "PVALIDATE CF=1 (double-validation) at GPA {:#x}; possible \
                         hypervisor page-aliasing attack",
                        addr.as_u64()
                    );
                }
                other => Err(other),
            },
        )
    }
}

trait PageStateChange {
    fn page_state_change(&self, assignment: MsrPageAssignment) -> Result<(), &'static str>;
}

impl<S: NotGiantPageSize> PageStateChange for PhysFrameRange<S> {
    fn page_state_change(&self, assignment: MsrPageAssignment) -> Result<(), &'static str> {
        // Future optimization: do this operation in batches of 253 frames (that's how
        // many can fit in one PageStateChange request) instead of one at a time.
        for frame in *self {
            GHCB_WRAPPER
                .get()
                .expect("GHCB not initialized")
                .page_state_change(frame, assignment)?;
        }

        Ok(())
    }
}

/// Calls `PVALIDATE` on all memory ranges specified in the E820 table with type
/// `RAM`.
pub fn validate_memory(e820_table: &[BootE820Entry]) {
    log::info!("starting SEV-SNP memory validation");

    let mut page_tables = oak_stage0::paging::PAGE_TABLE_REFS.get().unwrap().lock();

    // Page directory, for validation with 2 MiB pages.
    let mut validation_pd = MappedPage::new(VirtAddr::new(Size1GiB::SIZE)).unwrap();
    // For virtual address space, we currently shouldn't have anything at the second
    // gigabyte, so we can map the page to virtual address [1 GiB..2 GiB).
    if page_tables.pdpt[1].flags().contains(PageTableFlags::PRESENT) {
        panic!("PDPT[1] is in use");
    }
    page_tables.pdpt[1]
        .set_lower_level_table::<Sev>(validation_pd.page_table.as_ref(), PageTableFlags::PRESENT);

    // Page table, for validation with 4 KiB pages.
    let mut validation_pt = MappedPage::new(VirtAddr::new(Size2MiB::SIZE)).unwrap();
    // Find a location for our (temporary) page table. The initial page tables map
    // [0..2MiB), so it should be safe to put our temporary mappings at
    // [2..4MiB).
    if page_tables.pd_0[1].flags().contains(PageTableFlags::PRESENT) {
        panic!("PD_0[1] is in use");
    }
    page_tables.pd_0[1]
        .set_lower_level_table::<Sev>(validation_pt.page_table.as_ref(), PageTableFlags::PRESENT);

    // We already pvalidated the memory in the first 640KiB of RAM in the boot
    // assembly code. We avoid redoing this as calling pvalidate again on these
    // pages leads to unexpected results, such us removing the shared state from
    // the RMP for the fw_cfg DMA buffer.
    let min_addr = 0xA0000;

    // SECURITY: The stage0 firmware ROM is mapped just below 4 GiB and was
    // launched as PAGE_TYPE_NORMAL (RMP.Validated=1) by SNP_LAUNCH_UPDATE. A
    // malicious hypervisor must not be able to make us issue PSC+PVALIDATE over
    // those GPAs, or it can create validated page aliases for our own .text/.rodata
    // (SNP double-validation attack). The PCI hole means no legitimate RAM lives
    // here on a PC platform; we conservatively forbid the top 16 MiB below 4 GiB.
    const ROM_GUARD_START: usize = 0xFF00_0000; // 4 GiB - 16 MiB
    const ROM_GUARD_END: usize = 0x1_0000_0000; // 4 GiB

    for entry in e820_table {
        if entry.entry_type() != Some(E820EntryType::RAM) || entry.addr() < min_addr {
            continue;
        }

        // addr and size come straight from the hypervisor-supplied E820 table, so
        // the end of the range can overflow usize and either bound can exceed the
        // valid physical address width. Reject such an entry here instead of
        // panicking in the arithmetic below, mirroring the checked_add already used
        // for the host-supplied length in the TD HOB walk.
        let Some(end) = entry.addr().checked_add(entry.size()) else {
            log::error!(
                "nonsensical entry in E820 table: [{:#x}, +{:#x})",
                entry.addr(),
                entry.size()
            );
            continue;
        };

        // Defense-in-depth: refuse to accept memory that overlaps the firmware ROM
        // window. The CF=1 panic above is the primary mitigation; this check makes
        // the attack fail before any PSC is even issued.
        if entry.addr() < ROM_GUARD_END && end > ROM_GUARD_START {
            panic!(
                "hypervisor-supplied E820 RAM entry [{:#x}, {:#x}) overlaps firmware ROM \
                 window; refusing to PVALIDATE",
                entry.addr(),
                end
            );
        }

        let (Ok(start), Ok(limit)) =
            (PhysAddr::try_new(entry.addr() as u64), PhysAddr::try_new(end as u64))
        else {
            log::error!("nonsensical entry in E820 table: [{:#x}, {:#x})", entry.addr(), end);
            continue;
        };
        let start_address = start.align_up(Size4KiB::SIZE);
        let limit_address = limit.align_down(Size4KiB::SIZE);

        if start_address > limit_address {
            log::error!(
                "nonsensical entry in E820 table: [{}, {})",
                entry.addr(),
                entry.addr() + entry.size()
            );
            continue;
        }

        // Attempt to validate as many pages as possible using 2 MiB pages (aka
        // hugepages).
        let hugepage_start = start_address.align_up(Size2MiB::SIZE);
        let hugepage_limit = limit_address.align_down(Size2MiB::SIZE);

        // If start_address == hugepage_start, we're aligned with 2M address boundary.
        // Otherwise, we need to process any 4K pages before the alignment.
        // Note that limit_address may be less than hugepage_start, which means that the
        // E820 entry was less than 2M in size and didn't cross a 2M boundary.
        if hugepage_start > start_address {
            let limit = core::cmp::min(hugepage_start, limit_address);
            // We know the addresses are aligned to at least 4K, so the unwraps are safe.
            let range = PhysFrame::<Size4KiB>::range(
                PhysFrame::from_start_address(start_address).unwrap(),
                PhysFrame::from_start_address(limit).unwrap(),
            );
            range.page_state_change(MsrPageAssignment::Private).unwrap();
            range.pvalidate(&mut validation_pt).expect("failed to validate memory");
        }

        // If hugepage_limit > hugepage_start, we've got some contiguous 2M chunks that
        // we can process as hugepages.
        if hugepage_limit > hugepage_start {
            // These unwraps can't fail as we've made sure that the addresses are 2
            // MiB-aligned.
            let range = PhysFrame::<Size2MiB>::range(
                PhysFrame::from_start_address(hugepage_start).unwrap(),
                PhysFrame::from_start_address(hugepage_limit).unwrap(),
            );
            range.page_state_change(MsrPageAssignment::Private).unwrap();
            range
                .pvalidate(&mut validation_pd, &mut validation_pt)
                .expect("failed to validate memory");
        }

        // And finally, we may have some trailing 4K pages in [hugepage_limit,
        // limit_address) that we need to process.
        if limit_address > hugepage_limit {
            let start = core::cmp::max(start_address, hugepage_limit);
            // We know the addresses are aligned to at least 4K, so the unwraps are safe.
            let range = PhysFrame::<Size4KiB>::range(
                PhysFrame::from_start_address(start).unwrap(),
                PhysFrame::from_start_address(limit_address).unwrap(),
            );
            range.page_state_change(MsrPageAssignment::Private).unwrap();
            range.pvalidate(&mut validation_pt).expect("failed to validate memory");
        }
    }

    // Locate the legacy SMBIOS range [0xF_0000, 0x10_0000) in the E820 table.
    // Unwrap() will panic if entry not found with expected start, size, and type.
    let legacy_smbios_range_entry = e820_table
        .iter()
        .find(|entry| {
            entry.addr() == 0xF_0000
                && entry.size() == 0x1_0000
                && entry.entry_type() == Some(E820EntryType::RESERVED)
        })
        .expect("couldn't find legacy SMBIOS memory range");

    // Pvalidate the legacy SMBIOS range since legacy code may scan this range for
    // the SMBIOS entry point table, even if the range is marked as reserved.
    let range = PhysFrame::<Size4KiB>::range(
        PhysFrame::from_start_address(PhysAddr::new(legacy_smbios_range_entry.addr() as u64))
            .unwrap(),
        PhysFrame::from_start_address(PhysAddr::new(
            (legacy_smbios_range_entry.addr() + legacy_smbios_range_entry.size()) as u64,
        ))
        .unwrap(),
    );
    range.pvalidate(&mut validation_pt).expect("failed to validate SMBIOS memory");

    // Safety: the E820 table indicates that this is the correct memory segment.
    let legacy_smbios_range_bytes = unsafe {
        core::slice::from_raw_parts_mut::<u8>(
            legacy_smbios_range_entry.addr() as *mut u8,
            legacy_smbios_range_entry.size(),
        )
    };
    // Zeroize the legacy SMBIOS range bytes to avoid legacy code reading garbage.
    legacy_smbios_range_bytes.zeroize();

    page_tables.pd_0[1].set_unused();
    page_tables.pdpt[1].set_unused();
    tlb::flush_all();
    log::info!("SEV-SNP memory validation complete.");
    log::info!("  Validated using 2 MiB pages: {}", counters::VALIDATED_2M.load(Ordering::SeqCst));
    log::info!("  Validated using 4 KiB pages: {}", counters::VALIDATED_4K.load(Ordering::SeqCst));
    log::info!(
        "  Valid state not updated: {}",
        counters::ERROR_VALIDATION_STATUS_NOT_UPDATED.load(Ordering::SeqCst)
    );
    log::info!(
        "  RMP page size mismatch errors (fallback to 4K): {}",
        counters::ERROR_FAIL_SIZE_MISMATCH.load(Ordering::SeqCst)
    );
}

pub fn change_frame_state(
    frame: PhysFrame<Size4KiB>,
    state: PageAssignment,
) -> Result<(), &'static str> {
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        let request = SnpPageStateChangeRequest::new(
            frame.start_address().as_u64() as usize,
            state.into_msr(),
        )
        .expect("invalid address for page location");
        change_snp_page_state(request)?;
    }
    Ok(())
}

pub fn revalidate_page(page: Page<Size4KiB>) -> Result<(), &'static str> {
    if sev_status().contains(SevStatus::SEV_ENABLED) {
        let counter = AtomicUsize::new(0);
        match page.pvalidate(&counter) {
            Err(err) if err != InstructionError::ValidationStatusNotUpdated => {
                return Err("shared page revalidation failed");
            }
            _ => {}
        }
    }
    Ok(())
}
