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

use core::marker::PhantomData;
use x86_64::{
    structures::paging::{
        mapper::{MapToError, MapperFlush, PageTableFrameMapping},
        FrameAllocator, MappedPageTable, Mapper as BaseMapper, Page, PageSize, PageTable,
        PageTableFlags as BasePageTableFlags, PhysFrame, Size4KiB, Translate as BaseTranslate,
    },
    PhysAddr, VirtAddr,
};

use super::Translate;

#[derive(Clone, Copy)]
pub enum MemoryEncryption {
    /// Memory encryption is not supported. If `ENCRYPTED` page flag is set, it is ignored.
    NoEncryption,

    /// Memory encryption uses bit `C` in the page tables.
    ///
    /// The location of the C-bit is machine-dependent; it is reported by CPUID function 8000_001F
    /// in EBX[5:0].
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

bitflags::bitflags! {
    /// Possible flags for a page table entry.
    ///
    /// See <x86_64::structures::paging::PageTableFlags> for more details.
    pub struct PageTableFlags: u64 {
        const PRESENT = 1;
        const WRITABLE = 1 << 1;
        const USER_ACCESSIBLE = 1 << 2;
        const WRITE_THROUGH = 1 << 3;
        const NO_CACHE = 1 << 4;
        const ACCESSED = 1<< 5;
        const DIRTY = 1 << 6;
        const HUGE_PAGE = 1 << 7;
        const GLOBAL = 1 << 8;
        /// Marks the page as encrypted. Ignored under <NoEncryption>.
        ///
        /// The bit value is hardcoded to be 51 here, but that's because it's not possible to
        /// represent `ENCRYPTED = 1 << C` in Rust right now. The actual bit set may not be 51.
        const ENCRYPTED = 1 << 51;
        const NO_EXECUTE = 1 << 63;
    }
}

impl From<PageTableFlags> for BasePageTableFlags {
    fn from(value: PageTableFlags) -> Self {
        let mut flags = BasePageTableFlags::empty();
        if value.contains(PageTableFlags::PRESENT) {
            flags |= BasePageTableFlags::PRESENT
        }
        if value.contains(PageTableFlags::WRITABLE) {
            flags |= BasePageTableFlags::WRITABLE
        }
        if value.contains(PageTableFlags::USER_ACCESSIBLE) {
            flags |= BasePageTableFlags::USER_ACCESSIBLE
        }
        if value.contains(PageTableFlags::WRITE_THROUGH) {
            flags |= BasePageTableFlags::WRITE_THROUGH
        }
        if value.contains(PageTableFlags::NO_CACHE) {
            flags |= BasePageTableFlags::NO_CACHE
        }
        if value.contains(PageTableFlags::ACCESSED) {
            flags |= BasePageTableFlags::ACCESSED
        }
        if value.contains(PageTableFlags::DIRTY) {
            flags |= BasePageTableFlags::DIRTY
        }
        if value.contains(PageTableFlags::HUGE_PAGE) {
            flags |= BasePageTableFlags::HUGE_PAGE
        }
        if value.contains(PageTableFlags::GLOBAL) {
            flags |= BasePageTableFlags::GLOBAL
        }
        // There is no equivalent of ENCRYPTED in BasePageTableFlags.
        if value.contains(PageTableFlags::NO_EXECUTE) {
            flags |= BasePageTableFlags::NO_EXECUTE
        }
        flags
    }
}

/// Helper for mapper that assumes all memory is mapped to a given fixed offset.
///
/// See <x86_64::structures::paging::mapper::PageTableFrameMapping> for more details.
struct PhysOffset {
    offset: VirtAddr,
    encryption: MemoryEncryption,
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
        match self.encryption {
            // Frame allocator with no memory encryption: just delegate to the inner allocator.
            MemoryEncryption::NoEncryption => self.inner.allocate_frame(),
            // Frame allocator with memory encryption: tack on the encrypted bit.
            MemoryEncryption::Encrypted(c) => {
                let start_address = self.inner.allocate_frame()?.start_address() + (1u64 << c);
                Some(PhysFrame::from_start_address(start_address).unwrap())
            }
        }
    }
}

/// Page mapper for pages of type <S>
///
/// This is equivalent to <x86_64::structures::paging::mapper::Mapper>, but knows about memory
/// encryption.
pub trait Mapper<S: PageSize> {
    unsafe fn map_to_with_table_flags<A>(
        &mut self,
        page: Page<S>,
        frame: PhysFrame<S>,
        flags: PageTableFlags,
        parent_table_flags: PageTableFlags,
        frame_allocator: &mut A,
    ) -> Result<MapperFlush<S>, MapToError<S>>
    where
        A: FrameAllocator<Size4KiB>;
}

pub struct EncryptedPageTable<'a> {
    encryption: MemoryEncryption,
    offset: VirtAddr,
    inner: MappedPageTable<'a, PhysOffset>,
}

impl<'a> EncryptedPageTable<'a> {
    pub fn new(pml4: &'a mut PageTable, offset: VirtAddr, encryption: MemoryEncryption) -> Self {
        Self {
            encryption,
            offset,
            inner: unsafe { MappedPageTable::new(pml4, PhysOffset { offset, encryption }) },
        }
    }
}

impl<'a, S: PageSize> Mapper<S> for EncryptedPageTable<'a>
where
    MappedPageTable<'a, PhysOffset>: x86_64::structures::paging::Mapper<S>,
{
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
        let frame = match self.encryption {
            MemoryEncryption::Encrypted(c) if flags.contains(PageTableFlags::ENCRYPTED) => {
                PhysFrame::from_start_address(frame.start_address() + (1u64 << c)).unwrap()
            }
            _ => frame,
        };

        self.inner.map_to_with_table_flags(
            page,
            frame,
            flags.into(),
            parent_table_flags.into(),
            &mut EncryptedFrameAllocator::new(frame_allocator, self.encryption),
        )
    }
}

impl<'a> Translate for EncryptedPageTable<'a> {
    fn translate(&self, addr: VirtAddr) -> Option<PhysAddr> {
        match self.encryption {
            MemoryEncryption::Encrypted(c) => Some(PhysAddr::new(
                self.inner.translate_addr(addr)?.as_u64() & !(1u64 << c),
            )),
            MemoryEncryption::NoEncryption => self.inner.translate_addr(addr),
        }
    }

    fn translate_addr(&self, addr: PhysAddr) -> Option<VirtAddr> {
        Some(self.offset + addr.as_u64())
    }

    fn translate_frame<S: PageSize>(&self, frame: PhysFrame<S>) -> Option<Page<S>> {
        Page::from_start_address(self.translate_addr(frame.start_address())?).ok()
    }
}
