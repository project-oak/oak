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

use goblin::elf64::program_header::{PF_W, PF_X, PT_LOAD, ProgramHeader};
use x86_64::{
    PhysAddr, VirtAddr, align_down, align_up,
    registers::control::{Cr3, Cr3Flags},
    structures::paging::{
        MappedPageTable, Page, PageSize, PageTable, PhysFrame, Size2MiB, Size4KiB,
        frame::PhysFrameRange,
        mapper::{FlagUpdateError, MapToError, MapperFlush, UnmapError},
        page::PageRange,
    },
};

use super::{
    KERNEL_OFFSET, Mapper, PageTableFlags, Translator,
    encrypted_mapper::{EncryptedPageTable, MemoryEncryption, PhysOffset},
};

/// Map a region of physical memory to a virtual address using 2 MiB pages.
///
/// ## Safety
///
/// There are many ways you can cause memory safety errors and undefined
/// behaviour when creating page mappings. See <Mapper::map_to_with_table_flags>
/// for examples.
pub unsafe fn create_offset_map<S: PageSize, M: Mapper<S>>(
    range: PhysFrameRange<S>,
    offset: VirtAddr,
    flags: PageTableFlags,
    mapper: &mut M,
) -> Result<(), MapToError<S>> {
    for (i, frame) in range.enumerate() {
        // We don't set `PageTableFlags::GLOBAL` in `parent_table_flags` because Intel
        // and AMD CPUs behave differently (Intel ignores the `G` bit in parent
        // page table entries, AMD ignores it in lower entries _except_ PML4 and
        // PML5); the `G` bit has semantic meaning only in the lowest level of
        // page tables.
        unsafe {
            mapper
                .map_to_with_table_flags(
                    Page::<S>::from_start_address(offset + (i as u64) * S::SIZE).unwrap(),
                    frame,
                    flags,
                    PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::ENCRYPTED,
                )?
                .ignore();
        }
    }
    Ok(())
}

/// Maps the kernel memory ranges (ie. vaddr in last 2GB of memory), respecting
/// section permissions.
///
/// Strictly speaking there's nothing int he ELF file that _requires_ sections
/// to be page-aligned. It's entirely possible to have a section with write
/// privileges and a section with execute privileges be on the same 4K page --
/// which would defeat the purpose of restricting the permissions, as we'd have
/// to go for the lowest common denominator and mark the pages both writable and
/// executable. For now, calling this function fails if there is any overlap
/// when using 4K pages.
///
/// We also create mappings only for sections with vaddr above
/// 0xFFFF_FFFF_8000_0000, that is, for the memory range where the kernel code
/// should lie.
///
/// The mappings we create respect the `PF_W` and `PF_X` flags; there's no way
/// how to map a page as not readable (but still writable or executable), so
/// `PF_R` is ignored.
///
/// Note that even if this function returns an error, the page map may have been
/// partially updated.
///
/// # Safety
/// There are many ways you can cause memory safety errors and undefined
/// behaviour when creating page mappings. See <Mapper::map_to_with_table_flags>
/// for examples.
///
/// `EferFlags::NO_EXECUTE_ENABLE` needs to be enabled before loading the page
/// tables created by this function.
pub unsafe fn create_kernel_map<M: Mapper<Size2MiB> + Mapper<Size4KiB>>(
    program_headers: &[ProgramHeader],
    mapper: &mut M,
) -> Result<(), MapToError<Size4KiB>> {
    program_headers
        .iter()
        .filter(|phdr| phdr.p_type == PT_LOAD && phdr.p_vaddr >= KERNEL_OFFSET)
        .map(|phdr| {
            (
                PhysFrame::<Size4KiB>::range(
                    PhysFrame::from_start_address(PhysAddr::new(align_down(
                        phdr.p_paddr,
                        Size4KiB::SIZE,
                    )))
                    .unwrap(),
                    PhysFrame::from_start_address(PhysAddr::new(align_up(
                        phdr.p_paddr + phdr.p_memsz,
                        Size4KiB::SIZE,
                    )))
                    .unwrap(),
                ),
                VirtAddr::new(phdr.p_vaddr),
                /* It's not possible to mark a page not readable, so we ignore PF_R. */
                PageTableFlags::PRESENT
                    | PageTableFlags::GLOBAL
                    | PageTableFlags::ENCRYPTED
                    | if phdr.p_flags & PF_W > 0 {
                        PageTableFlags::WRITABLE
                    } else {
                        PageTableFlags::empty()
                    }
                    | if phdr.p_flags & PF_X == 0 {
                        PageTableFlags::NO_EXECUTE
                    } else {
                        PageTableFlags::empty()
                    },
            )
        })
        .try_for_each(|(range, offset, flags)| unsafe {
            create_offset_map(range, offset, flags, mapper)
        })
}

pub struct RootPageTable {
    inner: EncryptedPageTable<MappedPageTable<'static, PhysOffset>>,
}

impl RootPageTable {
    pub fn new(
        pml4: &'static mut PageTable,
        offset: VirtAddr,
        encryption: MemoryEncryption,
    ) -> Self {
        RootPageTable { inner: EncryptedPageTable::new(pml4, offset, encryption) }
    }
    pub fn into_inner(self) -> EncryptedPageTable<MappedPageTable<'static, PhysOffset>> {
        self.inner
    }
    /// Checks wheter all the pages in the range are unallocated.
    ///
    /// Even though the pages may be of arbitrary size, we check all
    /// 4KiB-aligned addresses in the range, as the mappings may be done
    /// with a smaller page size.
    ///
    /// If we find an address with a valid mapping, we return the page which
    /// contains a valid mapping.
    pub fn is_unallocated<S: PageSize>(&self, range: PageRange<S>) -> Result<(), Page<S>> {
        if let Some(item) = Page::<Size4KiB>::range(
            Page::containing_address(range.start.start_address()),
            Page::containing_address(range.end.start_address()),
        )
        .find(|page| self.translate_virtual(page.start_address()).is_some())
        {
            // We found a page that had a valid mapping in that range, bail out.
            Err(Page::<S>::containing_address(item.start_address()))
        } else {
            // No valid mappings found, the whole range is unmapped!
            Ok(())
        }
    }

    /// Finds a range of unallocated pages of the requested size.
    ///
    /// Args:
    ///   - start: the pages must start at, or after, `start`
    ///   - count: number of pages to allocate
    ///
    /// Returns:
    /// The range of unallocated pages, if there was a big enough unallocated
    /// gap in the virtual address space. The range may start at exactly
    /// `start`.
    pub fn find_unallocated_pages<S: PageSize>(
        &self,
        mut start: Page<S>,
        count: usize,
    ) -> Option<PageRange<S>> {
        // This is highly inefficient, but it should be called rarely enough that it
        // doesn't matter (famous last words...)
        // We assume virtual addresses are 48 bits, with the gap in the middle.
        let limit = Page::containing_address(if start.start_address().as_u64() < u64::pow(2, 47) {
            VirtAddr::new(u64::pow(2, 47) - 1)
        } else {
            VirtAddr::new(0xFFFF_FFFF_FFFF_FFFF - 1)
        });
        while start < limit {
            let range = Page::range(start, start + count as u64);

            // If it turns out something in that range was allocated, we move forward to the
            // page after that and try again.
            match self.is_unallocated(range) {
                Ok(()) => return Some(range),
                Err(page) => start = page + 1,
            }
        }

        // given the size of the 64-bit address space, this should never happen
        None
    }
}

impl Mapper<Size4KiB> for RootPageTable {
    unsafe fn map_to_with_table_flags(
        &self,
        page: Page<Size4KiB>,
        frame: PhysFrame<Size4KiB>,
        flags: PageTableFlags,
        parent_table_flags: PageTableFlags,
    ) -> Result<MapperFlush<Size4KiB>, MapToError<Size4KiB>> {
        unsafe { self.inner.map_to_with_table_flags(page, frame, flags, parent_table_flags) }
    }

    unsafe fn unmap(
        &self,
        page: Page<Size4KiB>,
    ) -> Result<(PhysFrame<Size4KiB>, MapperFlush<Size4KiB>), UnmapError> {
        unsafe { self.inner.unmap(page) }
    }

    unsafe fn update_flags(
        &self,
        page: Page<Size4KiB>,
        flags: PageTableFlags,
    ) -> Result<MapperFlush<Size4KiB>, FlagUpdateError> {
        unsafe { self.inner.update_flags(page, flags) }
    }
}

impl Mapper<Size2MiB> for RootPageTable {
    unsafe fn map_to_with_table_flags(
        &self,
        page: Page<Size2MiB>,
        frame: PhysFrame<Size2MiB>,
        flags: PageTableFlags,
        parent_table_flags: PageTableFlags,
    ) -> Result<MapperFlush<Size2MiB>, MapToError<Size2MiB>> {
        unsafe { self.inner.map_to_with_table_flags(page, frame, flags, parent_table_flags) }
    }

    unsafe fn unmap(
        &self,
        page: Page<Size2MiB>,
    ) -> Result<(PhysFrame<Size2MiB>, MapperFlush<Size2MiB>), UnmapError> {
        unsafe { self.inner.unmap(page) }
    }

    unsafe fn update_flags(
        &self,
        page: Page<Size2MiB>,
        flags: PageTableFlags,
    ) -> Result<MapperFlush<Size2MiB>, FlagUpdateError> {
        unsafe { self.inner.update_flags(page, flags) }
    }
}

impl Translator for RootPageTable {
    fn translate_virtual(&self, addr: VirtAddr) -> Option<PhysAddr> {
        self.inner.translate_virtual(addr)
    }

    fn translate_physical(&self, addr: PhysAddr) -> Option<VirtAddr> {
        self.inner.translate_physical(addr)
    }

    fn translate_physical_frame<S: PageSize>(&self, frame: PhysFrame<S>) -> Option<Page<S>> {
        self.inner.translate_physical_frame(frame)
    }
}

/// Wrapper struct that holds the current page table is there one.
pub struct CurrentRootPageTable {
    inner: Option<RootPageTable>,
}

impl CurrentRootPageTable {
    pub const fn empty() -> Self {
        Self { inner: None }
    }

    /// Replaces the current pagetable with the parameter, returning the old
    /// pagetable if there was one. Updates the page table on the CPU level.
    /// Safety: The new page tables must keep the identity mapping at -2GB
    /// (kernel space) intact.
    pub unsafe fn replace(&mut self, pml4_frame: PhysFrame) -> Option<RootPageTable> {
        log::debug!("Writing new frame to Cr3: {:?}", pml4_frame);
        // This validates any references that expect boot page tables to be valid!
        // Safety: Caller must ensure that the new page tables are safe.
        unsafe {
            Cr3::write(pml4_frame, Cr3Flags::empty());
        };

        // Safety: we've reloaded page tables that place the direct mapping region at
        // that offset, so the memory location is safe to access now.
        let pml4 = unsafe {
            &mut *(super::DIRECT_MAPPING_OFFSET + pml4_frame.start_address().as_u64()).as_mut_ptr()
        };

        let new_pt = RootPageTable::new(pml4, super::DIRECT_MAPPING_OFFSET, super::encryption());

        self.inner.replace(new_pt)
    }

    /// Gets the reference to the underlying pagetable.
    ///
    /// Returns `None` if the pagetable has not yet been set.
    pub fn get(&self) -> Option<&RootPageTable> {
        self.inner.as_ref()
    }

    /// Gets the mutable reference to the underlying pagetable.
    ///
    /// Returns `None` if the pagetable has not yet been set.
    pub fn get_mut(&mut self) -> Option<&mut RootPageTable> {
        self.inner.as_mut()
    }
}
