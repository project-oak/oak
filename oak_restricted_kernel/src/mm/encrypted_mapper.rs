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

use super::{Mapper, PageTableFlags, Translator};
use core::marker::PhantomData;
use x86_64::{
    structures::paging::{
        mapper::{
            FlagUpdateError, MapToError, MapperAllSizes, MapperFlush, PageTableFrameMapping,
            UnmapError,
        },
        page::PageRange,
        FrameAllocator, MappedPageTable, Mapper as BaseMapper, Page, PageSize, PageTable,
        PhysFrame, Size4KiB, Translate as BaseTranslate,
    },
    PhysAddr, VirtAddr,
};

#[derive(Clone, Copy)]
pub enum MemoryEncryption {
    /// Memory encryption is not supported. If `ENCRYPTED` page flag is set, it is ignored.
    NoEncryption,

    /// Memory encryption uses bit `C` in the page tables.
    ///
    /// The location of the C-bit is machine-dependent; it is reported by CPUID function 8000_001F
    /// in EBX\[5:0\].
    /// See AMD64 Architecture Programmer's Manual, Volume 2, Section 15.34.1 and
    /// AMD64 Architecture Programmer's Manual, Volume 3, Section E.4.17 for more details.
    Encrypted(u8),
}

impl MemoryEncryption {
    pub fn bit(&self) -> u64 {
        match self {
            MemoryEncryption::NoEncryption => 0,
            MemoryEncryption::Encrypted(c) => 1u64 << c,
        }
    }
}

/// Helper for mapper that assumes all memory is mapped to a given fixed offset.
///
/// See <x86_64::structures::paging::mapper::PageTableFrameMapping> for more details.
pub struct PhysOffset {
    offset: VirtAddr,
    encryption: MemoryEncryption,
}

impl PhysOffset {
    pub fn new(offset: VirtAddr, encryption: MemoryEncryption) -> Self {
        PhysOffset { offset, encryption }
    }
}

unsafe impl PageTableFrameMapping for PhysOffset {
    fn frame_to_pointer(&self, frame: PhysFrame) -> *mut PageTable {
        let virt = self.offset
            + match self.encryption {
                // Mapping without encryption: just do the calculation using the offset.
                MemoryEncryption::NoEncryption => frame.start_address().as_u64(),
                // Mapping under encryption: strip off the encrypted bit before adding the offset.
                MemoryEncryption::Encrypted(c) => frame.start_address().as_u64() & !(1 << c),
            };
        virt.as_mut_ptr()
    }
}

/// Wrapper around `FrameAllocator` that sets the encrypted bit on the allocated frame, if needed.
///
/// This is only meant to be used inside `EncryptedPageTable` to lie to `MappedPageTable` about the
/// physical addresses.
struct EncryptedFrameAllocator<'a, S: PageSize, A: FrameAllocator<S>> {
    inner: &'a mut A,
    encryption: MemoryEncryption,
    phantom: PhantomData<S>,
}

impl<'a, S: PageSize, A: FrameAllocator<S>> EncryptedFrameAllocator<'a, S, A> {
    fn new(inner: &'a mut A, encryption: MemoryEncryption) -> Self {
        Self {
            inner,
            encryption,
            phantom: PhantomData,
        }
    }
}

unsafe impl<'a, S: PageSize, A: FrameAllocator<S>> FrameAllocator<S>
    for EncryptedFrameAllocator<'a, S, A>
{
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        let start_address = self.inner.allocate_frame()?.start_address() + self.encryption.bit();
        Some(PhysFrame::from_start_address(start_address).unwrap())
    }
}

/// Frame allocator that always fails to allocate.
///
/// This is useful in situations where we do not expect any new allocations to take place.
struct FailAllocator {}
unsafe impl<S: PageSize> FrameAllocator<S> for FailAllocator {
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        None
    }
}

pub struct EncryptedPageTable<N: MapperAllSizes> {
    encryption: MemoryEncryption,
    offset: VirtAddr,
    inner: N,
}

impl<'a> EncryptedPageTable<MappedPageTable<'a, PhysOffset>> {
    pub fn new(pml4: &'a mut PageTable, offset: VirtAddr, encryption: MemoryEncryption) -> Self {
        Self {
            encryption,
            offset,
            inner: unsafe { MappedPageTable::new(pml4, PhysOffset { offset, encryption }) },
        }
    }

    /// Finds a range of unallocated pages of the requested size.
    ///
    /// Args:
    ///   - start: the pages must start at, or after, `start`
    ///   - count: number of pages to allocate
    ///
    /// Returns:
    /// The range of unallocated pages, if there was a big enough unallocated gap in the virtual
    /// address space. The range may start at exactly `start`.
    pub fn find_unallocated_pages<S: PageSize>(
        &self,
        mut start: Page<S>,
        count: usize,
    ) -> Option<PageRange<S>> {
        // This is highly inefficient, but it should be called rarely enough that it doesn't matter
        // (famous last words...)
        // We assume virtual addresses are 48 bits, with the gap in the middle.
        let limit = Page::containing_address(if start.start_address().as_u64() < u64::pow(2, 47) {
            VirtAddr::new(u64::pow(2, 47) - 1)
        } else {
            VirtAddr::new(0xFFFF_FFFF_FFFF_FFFF - 1)
        });
        while start < limit {
            let range = Page::range(start, start + count as u64);

            match self.is_unallocated(range) {
                Ok(()) => return Some(range),
                Err(page) => {
                    start = page + 1;
                }
            }
        }

        // given the size of the 64-bit address space, this should never happen
        None
    }

    /// Checks wheter all the pages in the range are unallocated.
    ///
    /// Even though the pages may be of arbitrary size, we check all 4KiB-aligned addresses in the
    /// range, as the mappings may be done with a smaller page size.
    ///
    /// If we find an address with a valid mapping, we return the page which contains a valid
    /// mapping.
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
}

impl<S: PageSize, N: MapperAllSizes + BaseMapper<S>> Mapper<S> for EncryptedPageTable<N> {
    unsafe fn map_to_with_table_flags<A>(
        &mut self,
        page: Page<S>,
        frame: PhysFrame<S>,
        flags: PageTableFlags,
        parent_table_flags: PageTableFlags,
        frame_allocator: &mut A,
    ) -> Result<MapperFlush<S>, MapToError<S>>
    where
        A: FrameAllocator<Size4KiB>,
    {
        // Set the encrypted bit in the physical frame, if needed.
        let frame = if flags.contains(PageTableFlags::ENCRYPTED) {
            PhysFrame::from_start_address(frame.start_address() + self.encryption.bit()).unwrap()
        } else {
            frame
        };

        self.inner.map_to_with_table_flags(
            page,
            frame,
            flags.into(),
            parent_table_flags.into(),
            &mut EncryptedFrameAllocator::new(frame_allocator, self.encryption),
        )
    }

    unsafe fn unmap(
        &mut self,
        page: Page<S>,
    ) -> Result<(PhysFrame<S>, MapperFlush<S>), UnmapError> {
        let (frame, flush) = self.inner.unmap(page)?;
        // if the frame had the encrypted bit set, strip it
        let frame = PhysFrame::from_start_address(PhysAddr::new(
            frame.start_address().as_u64() & !self.encryption.bit(),
        ))
        .unwrap();
        Ok((frame, flush))
    }

    unsafe fn update_flags(
        &mut self,
        page: Page<S>,
        flags: PageTableFlags,
    ) -> Result<MapperFlush<S>, FlagUpdateError> {
        // `ENCRYPTED` requires special treatment, therefore it's easier to just re-map the page.
        let frame = match self.unmap(page) {
            Err(UnmapError::ParentEntryHugePage) => Err(FlagUpdateError::ParentEntryHugePage),
            Err(UnmapError::PageNotMapped) => Err(FlagUpdateError::PageNotMapped),
            Err(UnmapError::InvalidFrameAddress(addr)) => {
                panic!("page table entry points to invalid address: {:?}", addr)
            }
            Ok((frame, _)) => Ok(frame),
        }?;

        // We're remapping the page, therefore we shouldn't need a frame allocator nor
        // parent_table_flags, as we shouldn't be allocating new page tables.
        match self.map_to_with_table_flags(
            page,
            frame,
            flags,
            PageTableFlags::empty(),
            &mut FailAllocator {},
        ) {
            Ok(flush) => Ok(flush),
            // This should never happen, as we should not be allocating frames.
            Err(MapToError::FrameAllocationFailed) => {
                panic!("unexpected frame allocation when changing page table flags")
            }
            // This should never happen, as we've just unmapped the page.
            Err(MapToError::PageAlreadyMapped(page)) => panic!(
                "expected page {:?} to be unmapped, but it was still mapped",
                page
            ),
            Err(MapToError::ParentEntryHugePage) => Err(FlagUpdateError::ParentEntryHugePage),
        }
    }
}

impl<N: MapperAllSizes + BaseTranslate> Translator for EncryptedPageTable<N> {
    fn translate_virtual(&self, addr: VirtAddr) -> Option<PhysAddr> {
        Some(PhysAddr::new(
            self.inner.translate_addr(addr)?.as_u64() & !self.encryption.bit(),
        ))
    }

    fn translate_physical(&self, addr: PhysAddr) -> Option<VirtAddr> {
        Some(self.offset + addr.as_u64())
    }

    fn translate_physical_frame<S: PageSize>(&self, frame: PhysFrame<S>) -> Option<Page<S>> {
        Page::from_start_address(self.translate_physical(frame.start_address())?).ok()
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use x86_64::structures::paging::{
        mapper::{MappedFrame, TranslateResult},
        PageTableFlags as BasePageTableFlags, Size1GiB, Size2MiB,
    };

    use super::*;

    #[test]
    fn phys_offset_encrypted() {
        let phys_offset = PhysOffset {
            offset: VirtAddr::new(0x12345000),
            encryption: MemoryEncryption::Encrypted(51),
        };
        assert_eq!(
            phys_offset.frame_to_pointer(
                PhysFrame::from_start_address(PhysAddr::new(0x1000 + (1 << 51))).unwrap()
            ) as u64,
            0x12345000 + 0x1000
        );
        assert_eq!(
            phys_offset
                .frame_to_pointer(PhysFrame::from_start_address(PhysAddr::new(0x1000)).unwrap())
                as u64,
            0x12345000 + 0x1000
        );
    }

    #[test]
    #[should_panic]
    fn phys_offset_unencrypted_with_bit_set() {
        let phys_offset = PhysOffset {
            offset: VirtAddr::new(0x12345000),
            encryption: MemoryEncryption::NoEncryption,
        };
        assert_eq!(
            phys_offset.frame_to_pointer(
                PhysFrame::from_start_address(PhysAddr::new(0x1000 + (1 << 51))).unwrap()
            ) as u64,
            0x12345000 + 0x1000 + (1 << 51)
        );
    }

    #[test]
    fn phys_offset_unencrypted_without_bit_set() {
        let phys_offset = PhysOffset {
            offset: VirtAddr::new(0x12345000),
            encryption: MemoryEncryption::NoEncryption,
        };
        assert_eq!(
            phys_offset
                .frame_to_pointer(PhysFrame::from_start_address(PhysAddr::new(0x1000)).unwrap())
                as u64,
            0x12345000 + 0x1000
        );
    }

    struct FakeFrameAllocator {}
    unsafe impl<S: PageSize> FrameAllocator<S> for FakeFrameAllocator {
        fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
            Some(PhysFrame::from_start_address(PhysAddr::new(1u64 << 21)).unwrap())
        }
    }

    #[test]
    fn frame_allocator_unencrypted() {
        let mut inner = FakeFrameAllocator {};
        let mut frame_allocator: EncryptedFrameAllocator<'_, Size4KiB, _> =
            EncryptedFrameAllocator::new(&mut inner, MemoryEncryption::NoEncryption);
        assert_eq!(
            frame_allocator.allocate_frame().unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(1u64 << 21)).unwrap()
        )
    }

    #[test]
    fn frame_allocator_encrypted() {
        let mut inner = FakeFrameAllocator {};
        let mut frame_allocator: EncryptedFrameAllocator<'_, Size4KiB, _> =
            EncryptedFrameAllocator::new(&mut inner, MemoryEncryption::Encrypted(51));
        assert_eq!(
            frame_allocator.allocate_frame().unwrap(),
            PhysFrame::from_start_address(PhysAddr::new((1u64 << 21) + (1u64 << 51))).unwrap()
        )
    }

    struct FakeMapper {
        expected_phys_frame: PhysFrame<Size4KiB>,
    }

    impl BaseMapper<Size1GiB> for FakeMapper {
        unsafe fn map_to_with_table_flags<A>(
            &mut self,
            _page: Page<Size1GiB>,
            _frame: PhysFrame<Size1GiB>,
            _flags: BasePageTableFlags,
            _parent_table_flags: BasePageTableFlags,
            _frame_allocator: &mut A,
        ) -> Result<MapperFlush<Size1GiB>, MapToError<Size1GiB>>
        where
            Self: Sized,
            A: FrameAllocator<Size4KiB> + ?Sized,
        {
            unimplemented!()
        }

        fn unmap(
            &mut self,
            _page: Page<Size1GiB>,
        ) -> Result<
            (PhysFrame<Size1GiB>, MapperFlush<Size1GiB>),
            x86_64::structures::paging::mapper::UnmapError,
        > {
            unimplemented!()
        }

        unsafe fn update_flags(
            &mut self,
            _page: Page<Size1GiB>,
            _flags: BasePageTableFlags,
        ) -> Result<MapperFlush<Size1GiB>, x86_64::structures::paging::mapper::FlagUpdateError>
        {
            unimplemented!()
        }

        unsafe fn set_flags_p4_entry(
            &mut self,
            _page: Page<Size1GiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        unsafe fn set_flags_p3_entry(
            &mut self,
            _page: Page<Size1GiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        unsafe fn set_flags_p2_entry(
            &mut self,
            _page: Page<Size1GiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        fn translate_page(
            &self,
            _page: Page<Size1GiB>,
        ) -> Result<PhysFrame<Size1GiB>, x86_64::structures::paging::mapper::TranslateError>
        {
            unimplemented!()
        }
    }
    impl BaseMapper<Size2MiB> for FakeMapper {
        unsafe fn map_to_with_table_flags<A>(
            &mut self,
            _page: Page<Size2MiB>,
            _frame: PhysFrame<Size2MiB>,
            _flags: BasePageTableFlags,
            _parent_table_flags: BasePageTableFlags,
            _frame_allocator: &mut A,
        ) -> Result<MapperFlush<Size2MiB>, MapToError<Size2MiB>>
        where
            Self: Sized,
            A: FrameAllocator<Size4KiB> + ?Sized,
        {
            unimplemented!()
        }

        fn unmap(
            &mut self,
            _page: Page<Size2MiB>,
        ) -> Result<
            (PhysFrame<Size2MiB>, MapperFlush<Size2MiB>),
            x86_64::structures::paging::mapper::UnmapError,
        > {
            unimplemented!()
        }

        unsafe fn update_flags(
            &mut self,
            _page: Page<Size2MiB>,
            _flags: BasePageTableFlags,
        ) -> Result<MapperFlush<Size2MiB>, x86_64::structures::paging::mapper::FlagUpdateError>
        {
            unimplemented!()
        }

        unsafe fn set_flags_p4_entry(
            &mut self,
            _page: Page<Size2MiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        unsafe fn set_flags_p3_entry(
            &mut self,
            _page: Page<Size2MiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        unsafe fn set_flags_p2_entry(
            &mut self,
            _page: Page<Size2MiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        fn translate_page(
            &self,
            _page: Page<Size2MiB>,
        ) -> Result<PhysFrame<Size2MiB>, x86_64::structures::paging::mapper::TranslateError>
        {
            unimplemented!()
        }
    }
    impl BaseMapper<Size4KiB> for FakeMapper {
        unsafe fn map_to_with_table_flags<A>(
            &mut self,
            page: Page<Size4KiB>,
            frame: PhysFrame<Size4KiB>,
            _flags: BasePageTableFlags,
            _parent_table_flags: BasePageTableFlags,
            _frame_allocator: &mut A,
        ) -> Result<MapperFlush<Size4KiB>, MapToError<Size4KiB>>
        where
            Self: Sized,
            A: FrameAllocator<Size4KiB> + ?Sized,
        {
            assert_eq!(frame, self.expected_phys_frame);
            Ok(MapperFlush::new(page))
        }

        fn unmap(
            &mut self,
            page: Page<Size4KiB>,
        ) -> Result<
            (PhysFrame<Size4KiB>, MapperFlush<Size4KiB>),
            x86_64::structures::paging::mapper::UnmapError,
        > {
            Ok((
                PhysFrame::from_start_address(PhysAddr::new(
                    0x12340000 + page.start_address().as_u64(),
                ))
                .unwrap(),
                MapperFlush::new(page),
            ))
        }

        unsafe fn update_flags(
            &mut self,
            _page: Page<Size4KiB>,
            _flags: BasePageTableFlags,
        ) -> Result<MapperFlush<Size4KiB>, x86_64::structures::paging::mapper::FlagUpdateError>
        {
            unimplemented!()
        }

        unsafe fn set_flags_p4_entry(
            &mut self,
            _page: Page<Size4KiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        unsafe fn set_flags_p3_entry(
            &mut self,
            _page: Page<Size4KiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        unsafe fn set_flags_p2_entry(
            &mut self,
            _page: Page<Size4KiB>,
            _flags: BasePageTableFlags,
        ) -> Result<
            x86_64::structures::paging::mapper::MapperFlushAll,
            x86_64::structures::paging::mapper::FlagUpdateError,
        > {
            unimplemented!()
        }

        fn translate_page(
            &self,
            _page: Page<Size4KiB>,
        ) -> Result<PhysFrame<Size4KiB>, x86_64::structures::paging::mapper::TranslateError>
        {
            unimplemented!()
        }
    }
    impl BaseTranslate for FakeMapper {
        fn translate(&self, addr: VirtAddr) -> TranslateResult {
            TranslateResult::Mapped {
                frame: MappedFrame::Size4KiB(
                    PhysFrame::from_start_address(PhysAddr::new(addr.as_u64() - 0x12340000))
                        .unwrap(),
                ),
                offset: 0,
                flags: BasePageTableFlags::empty(),
            }
        }
    }

    #[test]
    fn mapper_unencrypted() {
        let mut mapper = EncryptedPageTable {
            encryption: MemoryEncryption::NoEncryption,
            offset: VirtAddr::new(0x1234000),
            inner: FakeMapper {
                expected_phys_frame: PhysFrame::from_start_address(PhysAddr::new(0x12341000))
                    .unwrap(),
            },
        };

        unsafe {
            mapper
                .map_to_with_table_flags(
                    Page::<Size4KiB>::from_start_address(VirtAddr::new(0x1000)).unwrap(),
                    PhysFrame::from_start_address(PhysAddr::new(0x12341000)).unwrap(),
                    PageTableFlags::ENCRYPTED,
                    PageTableFlags::ENCRYPTED,
                    &mut FakeFrameAllocator {},
                )
                .unwrap()
                .ignore();
        }

        assert_eq!(
            mapper.translate_virtual(VirtAddr::new(0x12341000)).unwrap(),
            PhysAddr::new(0x1000)
        );
    }

    #[test]
    fn mapper_encrypted() {
        let mut mapper = EncryptedPageTable {
            encryption: MemoryEncryption::Encrypted(51),
            offset: VirtAddr::new(0x1234000),
            inner: FakeMapper {
                expected_phys_frame: PhysFrame::from_start_address(PhysAddr::new(
                    0x12341000 + (1u64 << 51),
                ))
                .unwrap(),
            },
        };

        unsafe {
            mapper
                .map_to_with_table_flags(
                    Page::<Size4KiB>::from_start_address(VirtAddr::new(0x1000)).unwrap(),
                    PhysFrame::from_start_address(PhysAddr::new(0x12341000)).unwrap(),
                    PageTableFlags::ENCRYPTED,
                    PageTableFlags::ENCRYPTED,
                    &mut FakeFrameAllocator {},
                )
                .unwrap()
                .ignore();
        }

        assert_eq!(
            mapper.translate_virtual(VirtAddr::new(0x12341000)).unwrap(),
            PhysAddr::new(0x1000)
        );
    }

    #[test]
    fn remap_encrypted() {
        let mut mapper = EncryptedPageTable {
            encryption: MemoryEncryption::Encrypted(51),
            offset: VirtAddr::new(0x1234000),
            inner: FakeMapper {
                expected_phys_frame: PhysFrame::from_start_address(PhysAddr::new(
                    0x12341000 + (1u64 << 51),
                ))
                .unwrap(),
            },
        };

        unsafe {
            mapper
                .update_flags(
                    Page::<Size4KiB>::from_start_address(VirtAddr::new(0x1000)).unwrap(),
                    PageTableFlags::ENCRYPTED,
                )
                .unwrap()
                .ignore();
        }

        let mut mapper = EncryptedPageTable {
            encryption: MemoryEncryption::Encrypted(51),
            offset: VirtAddr::new(0x1234000),
            inner: FakeMapper {
                expected_phys_frame: PhysFrame::from_start_address(PhysAddr::new(0x12341000))
                    .unwrap(),
            },
        };

        unsafe {
            mapper
                .update_flags(
                    Page::<Size4KiB>::from_start_address(VirtAddr::new(0x1000)).unwrap(),
                    PageTableFlags::empty(),
                )
                .unwrap()
                .ignore();
        }
    }

    #[test]
    fn remap_unencrypted() {
        let mut mapper = EncryptedPageTable {
            encryption: MemoryEncryption::NoEncryption,
            offset: VirtAddr::new(0x1234000),
            inner: FakeMapper {
                expected_phys_frame: PhysFrame::from_start_address(PhysAddr::new(0x12341000))
                    .unwrap(),
            },
        };

        unsafe {
            mapper
                .update_flags(
                    Page::<Size4KiB>::from_start_address(VirtAddr::new(0x1000)).unwrap(),
                    PageTableFlags::ENCRYPTED,
                )
                .unwrap()
                .ignore();

            mapper
                .update_flags(
                    Page::<Size4KiB>::from_start_address(VirtAddr::new(0x1000)).unwrap(),
                    PageTableFlags::empty(),
                )
                .unwrap()
                .ignore();
        }
    }
}
