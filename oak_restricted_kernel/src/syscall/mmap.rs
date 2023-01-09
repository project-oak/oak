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

use crate::{
    mm::{Mapper, PageTableFlags},
    FRAME_ALLOCATOR, PAGE_TABLES,
};
use core::{
    cmp::max,
    ffi::{c_int, c_size_t, c_void},
    iter::repeat_with,
    ops::DerefMut,
    ptr::NonNull,
};
use oak_restricted_kernel_interface::{
    syscalls::{MmapFlags, MmapProtection},
    Errno,
};
use x86_64::{
    align_up,
    structures::paging::{FrameAllocator, Page, PageSize, Size2MiB},
    VirtAddr,
};

fn mmap(
    addr: *const c_void,
    size: usize,
    prot: MmapProtection,
    flags: MmapFlags,
) -> Result<NonNull<c_void>, Errno> {
    if size == 0 {
        log::warn!("invalid size passed to mmap: {}", size);
        return Err(Errno::EINVAL);
    }

    if !flags.contains(MmapFlags::MAP_ANONYMOUS) || !flags.contains(MmapFlags::MAP_PRIVATE) {
        log::warn!("invalid flags passed to mmap: {:?}", flags);
        return Err(Errno::EINVAL);
    }

    // Don't touch anything below 2 MiB boundary (we don't want to make 0x0 a valid address); also,
    // make sure that the address is aligned to 2 MiB boundary.
    let addr = VirtAddr::new(max(addr as u64, Size2MiB::SIZE)).align_up(Size2MiB::SIZE);

    // We only deal with 2 MiB pages, so round `size` up to the closest 2 MiB boundary as well.
    let size = align_up(size as u64, Size2MiB::SIZE) as usize;
    let count = size / Size2MiB::SIZE as usize;

    // Allocate enough physical frames to cover the request.
    // Iterator that keeps allocating physical frames.
    let frames = repeat_with(|| FRAME_ALLOCATOR.get().unwrap().lock().allocate_frame());

    let flags = PageTableFlags::PRESENT
        | PageTableFlags::USER_ACCESSIBLE
        | PageTableFlags::ENCRYPTED
        | if prot.contains(MmapProtection::PROT_EXEC) {
            PageTableFlags::empty()
        } else {
            PageTableFlags::NO_EXECUTE
        }
        | if prot.contains(MmapProtection::PROT_WRITE) {
            PageTableFlags::WRITABLE
        } else {
            PageTableFlags::empty()
        };

    let pages = {
        // This critical section is rather long...
        let mut pt = PAGE_TABLES.get().unwrap().lock();

        // Now, find a gap in the page tables that satisifies the following:
        //  - in the lower half of virtual memory (user space)
        //  - greater or equal to `addr`
        //  - of at least size `size` (with size rounded up to the next 2 MiB boundary)
        let pages = pt
            .find_unallocated_pages(Page::<Size2MiB>::containing_address(addr), count)
            .ok_or(Errno::ENOMEM)?;

        // For each page we also need a physical frame to back it to create a mapping.
        for (page, frame) in pages.zip(frames) {
            // Safety: find_unallocated_pages returns, well, unallocated pages and we've held the
            // lock all the time so we can be sure that nobody else has mapped those
            // pages.
            unsafe {
                pt.map_to_with_table_flags(
                    page,
                    frame.ok_or(Errno::ENOMEM)?,
                    flags,
                    PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::ENCRYPTED,
                    FRAME_ALLOCATOR.get().unwrap().lock().deref_mut(),
                )
                .map_err(|err| {
                    log::error!(
                        "error updating page tables for address {}: {:?}",
                        page.start_address().as_u64(),
                        err
                    );
                    Errno::ENOMEM
                })?
                .flush();
            }
        }

        pages
    };

    // Zero out the memory, as required by mmap() semantics.
    // Safety: we've just allocated and mapped that chunk of memory, so (a) we know it's valid and
    // (b) nobody else can have a reference to it yet.
    unsafe {
        core::ptr::write_bytes::<u8>(pages.start.start_address().as_mut_ptr(), 0u8, size);
    }

    // Given that we've just successfully altered the page table the start address can't reasonably
    // be null.
    Ok(NonNull::new(pages.start.start_address().as_mut_ptr())
        .expect("page range start address is null!"))
}

pub fn syscall_mmap(
    addr: *const c_void,
    size: c_size_t,
    prot: usize,
    flags: usize,
    fd: c_int,
    offset: usize,
) -> isize {
    if fd != -1 || offset != 0 {
        log::warn!(
            "mmap syscall called with invalid fd: {} or offset: {}",
            fd,
            offset
        );
    }
    let prot = if let Some(prot) = MmapProtection::from_bits(prot as i32) {
        prot
    } else {
        log::warn!("invalid protection flags passed to mmap: {}", prot);
        return Errno::EINVAL as isize;
    };

    let flags = if let Some(flags) = MmapFlags::from_bits(flags as i32) {
        flags
    } else {
        log::warn!("invalid flags passed to mmap: {}", flags);
        return Errno::EINVAL as isize;
    };

    mmap(addr, size, prot, flags).map_or_else(|err| err as isize, |ptr| ptr.as_ptr() as isize)
}
