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
//

use alloc::alloc::{alloc, dealloc};
use core::alloc::Layout;

use x86_64::{
    instructions::tlb::flush_all,
    structures::paging::{PageSize, PageTableFlags, Size2MiB},
    PhysAddr, VirtAddr,
};

use crate::paging::PAGE_TABLE_REFS;

pub struct Mmio<S: PageSize> {
    pub base_address: x86_64::PhysAddr,
    layout: Layout,
    mmio_memory: *mut u32,
    phantom: core::marker::PhantomData<S>,
}

impl<S: PageSize> Mmio<S> {
    pub unsafe fn new(base_address: x86_64::PhysAddr) -> Self {
        // Tehcnically we only need a chunk of virtual memory (as we remap the physical
        // memory backing it anyway), but the easiest way how to get a chunk of virtual
        // memory is just to allocate it using the normal mechanisms. This means there
        // will be a chunk of physical memory sitting unmapped and unused, but that
        // should not matter for our use case.
        let layout = Layout::from_size_align(S::SIZE as usize, S::SIZE as usize).unwrap();
        let mmio_memory = alloc(layout).cast();

        // Remap our mmio_memory to base_address.
        if mmio_memory as u64 > Size2MiB::SIZE {
            panic!("MMIO memory virtual address does not land in the first page table");
        }
        let mut tables = PAGE_TABLE_REFS.get().unwrap().lock();
        tables.pt_0[VirtAddr::from_ptr(mmio_memory).p1_index()].set_addr(
            base_address,
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_CACHE,
        );
        flush_all();

        Mmio { base_address, layout, mmio_memory, phantom: core::marker::PhantomData }
    }

    pub fn read_u32(&self, offset: usize) -> u32 {
        // Safety:
        //   - offset is aligned to u32
        //   - we've checked it's within the page size
        //   - when calling new() we were promised the memory is valid
        unsafe { self.mmio_memory.add(offset).read_volatile() }
    }

    pub unsafe fn write_u32(&mut self, offset: usize, value: u32) {
        // Safety:
        //   - offset is aligned to u32
        //   - we've checked it's within the page size
        //   - when calling new() we were promised the memory is valid
        //   - the caller needs to guarantee the value makes sense
        self.mmio_memory.add(offset).write_volatile(value)
    }
}

impl<S: PageSize> Drop for Mmio<S> {
    fn drop(&mut self) {
        // Restore the memory mapping and deallocate our chunk of memory. This assumes
        // identity mapping, which we generally have in stage0.
        let mut tables = PAGE_TABLE_REFS.get().unwrap().lock();
        tables.pt_0[VirtAddr::from_ptr(self.mmio_memory).p1_index()].set_addr(
            PhysAddr::new(self.mmio_memory as u64),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
        );
        flush_all();

        // Safety: we've allocated the memory from the global allocator with `alloc` in
        // `BaseMMIO::new` with the same layout.
        unsafe { dealloc(self.mmio_memory.cast(), self.layout) };
        todo!()
    }
}
