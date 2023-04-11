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

use bitflags::bitflags;
use oak_core::sync::OnceCell;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
pub use oak_sev_guest::ghcb::Ghcb;
use oak_sev_guest::{
    ghcb::GhcbProtocol,
    instructions::{pvalidate, InstructionError, PageSize as SevPageSize, Validation},
    msr::{
        change_snp_page_state, register_ghcb_location, PageAssignment, RegisterGhcbGpaRequest,
        SnpPageStateChangeRequest,
    },
};
use spinning_top::Spinlock;
use strum::FromRepr;
use x86_64::{
    instructions::tlb,
    registers::{control::Cr3, model_specific::Msr},
    structures::paging::{
        frame::PhysFrameRange, page::AddressNotAligned, Page, PageSize, PageTable, PageTableFlags,
        PhysFrame, Size1GiB, Size2MiB, Size4KiB,
    },
    PhysAddr, VirtAddr,
};

/// The cache memory type used with MTRR.  We only use Write-Protect mode which the Linux kernel
/// expects to be enabled by the firmware in order to enable SEV.
#[repr(u8)]
#[allow(dead_code)] // Remove if this is ever ported to a public crate.
#[derive(FromRepr)]
pub enum MemoryType {
    UC = 0, // Uncacheable.
    WC = 1, // Write-Combining.
    WT = 4, // Writethrough	Reads.
    WP = 5, // Write-Protect.
    WB = 6, // Writeback.
}

impl TryFrom<u8> for MemoryType {
    type Error = &'static str;
    fn try_from(value: u8) -> Result<MemoryType, &'static str> {
        match MemoryType::from_repr(value) {
            Some(memory_type) => Ok(memory_type),
            None => Err("invalid value for MemoryType"),
        }
    }
}

/// IA32_MTRR_DefType base model specific register.
/// See https://wiki.osdev.org/MTRR for documentation.
#[derive(Debug)]
pub struct MTRRDefType;

bitflags! {
    /// Flags of the MTRRDefType Register.
    pub struct MTRRDefTypeFlags: u64 {
        /// Set this to enable MTRR.
        const MTRR_ENABLE = 1 << 11;
        /// Set to enable fixed-range support.
        const FIXED_RANGE_ENABLE = 1 << 10;
    }
}

impl MTRRDefType {
    /// The underlying model specific register.
    const MSR: Msr = Msr::new(0x2ff);

    #[allow(dead_code)] // Remove if this is ever ported to a public crate.
    pub fn read() -> (MTRRDefTypeFlags, MemoryType) {
        let msr_value = Self::read_raw();
        let memory_type:Result<MemoryType, &'static str>  = (msr_value as u8).try_into();
        (
            MTRRDefTypeFlags::from_bits_truncate(msr_value),
            memory_type.unwrap(),
        )
    }

    fn read_raw() -> u64 {
        let msr_value = unsafe { Self::MSR.read() };
        msr_value.try_into().unwrap()
    }

    /// Write the MTRRDefType flags and caching mode, preserving reserved values.
    /// The Linux kernel requires the mode be set to `MemoryType::WP` since
    /// July, 2022, with this requirement back-ported to 5.15.X, or it will silently crash when
    /// SEV is enabled.
    ///
    /// The Linux kernel gives a warning that MTRR is not setup properly, which we can igore:
    /// [    0.120763] mtrr: your CPUs had inconsistent MTRRdefType settings
    /// [    0.121529] mtrr: probably your BIOS does not setup all CPUs.
    /// [    0.122245] mtrr: corrected configuration.
    ///
    /// ## Safety
    ///
    /// Unsafe in rare cases such as when ROM is memory mapped, and we write to ROM, in a mode that
    /// caches the write, although this would require unsafe code to do.
    ///
    /// When called with MTRRDefType::MTRR_ENABLE and MemoryType::WP, this operation is safe because
    /// this specific MSR and mode has been supported since the P6 family of Pentium processors
    /// (see https://en.wikipedia.org/wiki/Memory_type_range_register).
    pub unsafe fn write(flags: MTRRDefTypeFlags, default_type: MemoryType) {
        // Preserve values of reserved bits.
        let old_value = Self::read_raw();
        let reserved = old_value & !(MTRRDefTypeFlags::all().bits() | u8::MAX as u64);
        let new_value = reserved | flags.bits() | (default_type as u64);
        unsafe { Self::write_raw(new_value) }
    }

    unsafe fn write_raw(value: u64) {
        let mut msr = Self::MSR;
        unsafe {
            msr.write(value);
        }
    }
}

static GHCB_WRAPPER: OnceCell<Spinlock<GhcbProtocol<'static, Ghcb>>> = OnceCell::new();

struct PageTables {
    pub pdpt: &'static mut PageTable,
    pub pd: &'static mut PageTable,
}

/// Returns references to the currently active PDPT and PD.
fn get_page_tables(encrypted: u64) -> PageTables {
    let (pml4_frame, _) = Cr3::read();
    let pml4 =
        unsafe { &*((pml4_frame.start_address().as_u64() & !encrypted) as *const PageTable) };
    let pdpt = unsafe { &mut *((pml4[0].addr().as_u64() & !encrypted) as *mut PageTable) };
    let pd = unsafe { &mut *((pdpt[0].addr().as_u64() & !encrypted) as *mut PageTable) };
    PageTables { pdpt, pd }
}

pub fn init_ghcb(
    ghcb: &'static mut Ghcb,
    snp: bool,
    encrypted: u64,
) -> &'static Spinlock<GhcbProtocol<'static, Ghcb>> {
    let ghcb_addr = VirtAddr::from_ptr(ghcb as *const _);

    share_page(Page::containing_address(ghcb_addr), snp, encrypted);

    // SNP requires that the GHCB is registered with the hypervisor.
    if snp {
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
    GHCB_WRAPPER.get().unwrap()
}

/// Stops sharing the GHCB with the hypervisor when running with AMD SEV-SNP enabled.
pub fn deinit_ghcb() {
    let ghcb_addr = VirtAddr::new(GHCB_WRAPPER.get().unwrap().lock().get_gpa().as_u64());
    unshare_page(Page::containing_address(ghcb_addr));
}

/// Shares a single 4KiB page with the hypervisor.
pub fn share_page(page: Page<Size4KiB>, snp: bool, encrypted: u64) {
    let page_start = page.start_address().as_u64();
    // Remove the ENCRYPTED bit from the entry that maps the page.
    let PageTables { pdpt: _, pd } = get_page_tables(encrypted);
    let pt = unsafe { &mut *((pd[0].addr().as_u64() & !encrypted) as *mut PageTable) };
    let idx = (page_start / Size4KiB::SIZE) as usize;
    pt[idx].set_addr(
        PhysAddr::new(page_start),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );
    tlb::flush_all();

    // SNP requires extra handling beyond just removing the encrypted bit.
    if snp {
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

        if let Some((_, err)) = memory
            .page_table
            .iter()
            .zip(pages)
            .filter(|(entry, _)| !entry.is_unused())
            .map(|(entry, page)| (entry, page.pvalidate()))
            .map(|(entry, result)| (entry, result.or_else(|err| f(entry.addr(), err))))
            .find(|(_, result)| result.is_err())
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
            |addr, err| match err {
                InstructionError::ValidationStatusNotUpdated => {
                    let addr = addr.as_u64() & !encrypted;

                    // Failing validation for addresses < 1 MiB is fine, as that memory was
                    // validated in bootstrap assembly.
                    if addr < 0x100000 {
                        return Ok(());
                    }

                    log::warn!("validation status not updated for address {:#018x}", addr);
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
                other => {
                    log::error!(
                        "validation failure for address {:#018x}: {:?}",
                        addr.as_u64() & !encrypted,
                        other
                    );
                    Err(other)
                }
            },
        )
    }
}

/// Calls `PVALIDATE` on all memory ranges specified in the E820 table with type `RAM`.
pub fn validate_memory(e820_table: &[BootE820Entry], encrypted: u64) {
    log::info!("starting SEV-SNP memory validation");

    let PageTables { pdpt, pd } = get_page_tables(encrypted);

    // Page directory, for validation with 2 MiB pages.
    let mut validation_pd = MappedPage::new(VirtAddr::new(Size1GiB::SIZE)).unwrap();
    // For virtual address space, we currently shouldn't have anything at the second gigabyte, so we
    // can map the page to virtual address [1 GiB..2 GiB).
    if pdpt[1].flags().contains(PageTableFlags::PRESENT) {
        panic!("PDPT[1] is in use");
    }
    pdpt[1].set_addr(
        PhysAddr::new(&validation_pd.page_table as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT,
    );

    // Page table, for validation with 4 KiB pages.
    let mut validation_pt = MappedPage::new(VirtAddr::new(Size2MiB::SIZE)).unwrap();
    // Find a location for our (temporary) page table. The initial page tables map [0..2MiB), so it
    // should be safe to put our temporary mappings at [2..4MiB).
    if pd[1].flags().contains(PageTableFlags::PRESENT) {
        panic!("PD[1] is in use");
    }
    pd[1].set_addr(
        PhysAddr::new(&validation_pt.page_table as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT,
    );

    for entry in e820_table {
        if entry.entry_type() != Some(E820EntryType::RAM) {
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
    pd[1].set_unused();
    pdpt[1].set_unused();
    tlb::flush_all();
    log::info!("SEV-SNP memory validation complete.");
}
