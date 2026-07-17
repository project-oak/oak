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

use core::ops::DerefMut;

use goblin::{elf32::program_header::PT_LOAD, elf64::program_header::ProgramHeader};
use log::info;
use oak_hal::PageAssignment;
use oak_linux_boot_params::{BootE820Entry, E820EntryType, Ramdisk};
use x86_64::{
    PhysAddr, VirtAddr,
    addr::{align_down, align_up},
    structures::paging::{
        FrameAllocator, Page, PageSize, PageTable, PageTableFlags, PhysFrame, Size2MiB, Size4KiB,
        frame::PhysFrameRange,
        mapper::{Mapper, OffsetPageTable},
    },
};

use crate::{FRAME_ALLOCATOR, PAGE_TABLES, VMA_ALLOCATOR};

mod bitmap_frame_allocator;
pub mod frame_allocator;
pub mod page_tables;
pub mod virtual_address_allocator;

/// The start of kernel memory.
pub const KERNEL_OFFSET: u64 = 0xFFFF_FFFF_8000_0000;

/// Exclusive upper bound of user space: the end of the lower half of the 48-bit
/// virtual address space. User space is `0x0000_0000_0000_0000 ..=
/// 0x0000_7FFF_FFFF_FFFF` (see the memory layout table on [`initial_pml4`]);
/// this is the same split `find_unallocated_pages` and the userspace stack in
/// `processes.rs` rely on.
pub const USERSPACE_VIRT_END: u64 = 0x8000_0000_0000;

/// Returns `true` if the whole `[start, start + len)` byte range lies within
/// user space (the lower half) and does not wrap around the address space.
///
/// The range is accepted iff its exclusive end is `<= USERSPACE_VIRT_END`, so
/// the last accessible byte is at most `USERSPACE_VIRT_END - 1` (the final user
/// address). A zero-length range only requires `start` itself to be in range.
/// Note: being in user space does not imply the range is mapped; an unmapped
/// user address still faults when accessed.
pub fn is_user_range(start: u64, len: usize) -> bool {
    match start.checked_add(len as u64) {
        Some(end) => end <= USERSPACE_VIRT_END,
        None => false, // address-space wrap
    }
}

#[cfg(test)]
mod user_range_tests {
    use super::{USERSPACE_VIRT_END, is_user_range};

    #[test]
    fn accepts_normal_lower_half_range() {
        assert!(is_user_range(0x1000, 0x1000));
        assert!(is_user_range(0, 0)); // null, zero length
        // A range ending exactly at the boundary (last byte = USERSPACE_VIRT_END-1).
        assert!(is_user_range(USERSPACE_VIRT_END - 0x1000, 0x1000));
    }

    #[test]
    fn rejects_range_crossing_or_above_boundary() {
        // Starts at the first kernel-half address.
        assert!(!is_user_range(USERSPACE_VIRT_END, 1));
        // Lower-half start but the range spills one byte past the boundary.
        assert!(!is_user_range(USERSPACE_VIRT_END - 0x1000, 0x1001));
        // Kernel image address.
        assert!(!is_user_range(0xFFFF_FFFF_8000_0000, 8));
    }

    #[test]
    fn rejects_wrapping_range() {
        assert!(!is_user_range(u64::MAX, 1));
        assert!(!is_user_range(u64::MAX - 3, 16));
    }
}

/// A raw pointer supplied by user space (ring 3). It is *untrusted*: the wrapped
/// address cannot be turned into a slice without going through one of the
/// validating accessors below, which enforce that the requested byte range lies
/// fully within user space and does not wrap. `repr(transparent)` guarantees it
/// has the same ABI as the raw pointer, so it can be passed to the syscall entry
/// points without changing the calling convention.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct UserSpacePtr(*const core::ffi::c_void);

impl From<*const core::ffi::c_void> for UserSpacePtr {
    fn from(ptr: *const core::ffi::c_void) -> Self {
        UserSpacePtr(ptr)
    }
}

impl From<*mut core::ffi::c_void> for UserSpacePtr {
    fn from(ptr: *mut core::ffi::c_void) -> Self {
        UserSpacePtr(ptr as *const core::ffi::c_void)
    }
}

impl UserSpacePtr {
    /// Validate that `[ptr, ptr + len)` lies fully in user space and return the
    /// raw byte pointer. `None` means the range is outside user space or wraps
    /// (callers map this to `EFAULT`). Not called for `len == 0`; the accessors
    /// handle the empty case first.
    fn checked(self, len: usize) -> Option<*mut u8> {
        if is_user_range(self.0 as u64, len) {
            Some(self.0 as *mut u8)
        } else {
            None
        }
    }

    /// Borrow the user range `[ptr, ptr + len)` as an immutable byte slice.
    /// Returns an empty slice for `len == 0` (no memory is touched). `None` if
    /// the range is not fully within user space.
    ///
    /// # Safety
    /// The caller must ensure the user range stays mapped and is not aliased for
    /// the lifetime `'a` of the returned slice.
    pub unsafe fn as_bytes<'a>(self, len: usize) -> Option<&'a [u8]> {
        if len == 0 {
            return Some(&[]);
        }
        let ptr = self.checked(len)?;
        // Safety: `is_user_range` verified `[ptr, ptr + len)` is a non-wrapping
        // user-space range; the caller upholds the mapping/aliasing invariant.
        Some(unsafe { core::slice::from_raw_parts(ptr as *const u8, len) })
    }

    /// Mutable counterpart of [`Self::as_bytes`].
    ///
    /// # Safety
    /// As [`Self::as_bytes`], and the range must be uniquely borrowed for `'a`.
    pub unsafe fn as_bytes_mut<'a>(self, len: usize) -> Option<&'a mut [u8]> {
        if len == 0 {
            // A mutable empty-slice literal borrows a temporary and won't satisfy
            // `'a`; a dangling, aligned, non-null pointer is the sound way to build
            // a zero-length mutable slice.
            return Some(unsafe {
                core::slice::from_raw_parts_mut(core::ptr::NonNull::<u8>::dangling().as_ptr(), 0)
            });
        }
        let ptr = self.checked(len)?;
        // Safety: as above; the borrow is unique for `'a`.
        Some(unsafe { core::slice::from_raw_parts_mut(ptr, len) })
    }
}

/// The offset used for the direct mapping of all physical memory.
const DIRECT_MAPPING_OFFSET: VirtAddr = VirtAddr::new_truncate(0xFFFF_8800_0000_0000);

impl Translator for OffsetPageTable<'_> {
    fn translate_virtual(&self, addr: VirtAddr) -> Option<PhysAddr> {
        use x86_64::structures::paging::Translate;
        self.translate_addr(addr)
    }

    fn translate_physical(&self, addr: PhysAddr) -> Option<VirtAddr> {
        Some(self.phys_offset() + addr.as_u64())
    }

    fn translate_physical_frame<S: PageSize>(&self, frame: PhysFrame<S>) -> Option<Page<S>> {
        Page::from_start_address(self.translate_physical(frame.start_address())?).ok()
    }
}

// TODO(#3394): Move to a shared crate.
pub trait Translator {
    /// Translates the given virtual address to the physical address that it
    /// maps to.
    ///
    /// Returns `None` if there is no valid mapping for the given address.
    fn translate_virtual(&self, addr: VirtAddr) -> Option<PhysAddr>;

    /// Translate a physical address to a virtual address.
    ///
    /// Note that a physical address may be mapped multiple times. This function
    /// will always return the address from the directly mapped region,
    /// ignoring ohter mappings if they exist.
    fn translate_physical(&self, addr: PhysAddr) -> Option<VirtAddr>;

    /// Translate a physical frame to virtual page, using the directly mapped
    /// region.
    fn translate_physical_frame<S: PageSize>(&self, frame: PhysFrame<S>) -> Option<Page<S>>;
}

pub fn encryption_aware_page_table_flags(
    mut flags: PageTableFlags,
    assignment: PageAssignment,
) -> PageTableFlags {
    if crate::is_memory_encryption_enabled() {
        flags.set_encrypted(match assignment {
            PageAssignment::Private => true,
            PageAssignment::Shared => false,
        });
    }
    flags
}

pub fn init(memory_map: &[BootE820Entry], program_headers: &[ProgramHeader], ramdisk: &Ramdisk) {
    let mut alloc = FRAME_ALLOCATOR.lock();

    /* Step 1: mark all RAM as available (event though it may contain data!) */
    memory_map
        .iter()
        .inspect(|e| {
            info!(
                "E820 entry: [{:#018x}..{:#018x}) ({}), type {}",
                e.addr(),
                e.addr() + e.size(),
                e.size(),
                e.entry_type().unwrap()
            );
        })
        .filter(|e| e.entry_type() == Some(E820EntryType::RAM))
        .map(|e| {
            // Clip both ends, if necessary, to make sure that we are aligned with 2 MiB
            // pages.
            (
                PhysAddr::new(align_up(e.addr() as u64, Size2MiB::SIZE)),
                PhysAddr::new(align_down((e.addr() + e.size()) as u64, Size2MiB::SIZE)),
            )
        })
        .filter(|(start, limit)| limit > start)
        .map(|(start, limit)| {
            // Safety: align_down/align_up guarantees we're aligned to 2 MiB boundaries,
            // and we know there's _something_ in the memory range.
            PhysFrame::range(
                PhysFrame::from_start_address(start).unwrap(),
                PhysFrame::from_start_address(limit).unwrap(),
            )
        })
        .for_each(|range| alloc.mark_valid(range, true));

    // Step 2: mark known in-use regions as not available.

    // First, leave out the first 2 MiB as there be dragons (and bootloader data
    // structures)
    alloc.mark_valid(
        PhysFrame::range(
            PhysFrame::from_start_address(PhysAddr::new(0x0)).unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(Size2MiB::SIZE)).unwrap(),
        ),
        false,
    );

    // Second, mark every `PT_LOAD` section from the phdrs as used.
    program_headers
        .iter()
        .filter(|phdr| phdr.p_type == PT_LOAD)
        .map(|phdr| {
            // Align the physical addresses to 2 MiB boundaries, making them larger if
            // necessary.
            PhysFrame::range(
                PhysFrame::from_start_address(PhysAddr::new(align_down(
                    phdr.p_paddr,
                    Size2MiB::SIZE,
                )))
                .unwrap(),
                PhysFrame::from_start_address(PhysAddr::new(align_up(
                    phdr.p_paddr + phdr.p_memsz,
                    Size2MiB::SIZE,
                )))
                .unwrap(),
            )
        })
        .for_each(|range| {
            info!(
                "marking [{:#018x}..{:#018x}) as reserved",
                range.start.start_address().as_u64(),
                range.end.start_address().as_u64()
            );
            alloc.mark_valid(range, false)
        });

    let ramdisk_range = ramdisk_range(ramdisk);
    info!(
        "marking [{:#018x}..{:#018x}) as reserved (ramdisk)",
        ramdisk_range.start.start_address().as_u64(),
        ramdisk_range.end.start_address().as_u64()
    );
    alloc.mark_valid(ramdisk_range, false);
}

pub fn ramdisk_range(ramdisk: &Ramdisk) -> PhysFrameRange<Size2MiB> {
    PhysFrame::range(
        PhysFrame::<x86_64::structures::paging::Size2MiB>::from_start_address(PhysAddr::new(
            align_down(ramdisk.addr.into(), Size2MiB::SIZE),
        ))
        .unwrap(),
        PhysFrame::from_start_address(PhysAddr::new(align_up(
            (ramdisk.addr + ramdisk.size).into(),
            Size2MiB::SIZE,
        )))
        .unwrap(),
    )
}

/// Creates the initial page tables used by the kernel.
///
/// The memory layout we follow is largely based on the Linux layout
/// (<https://www.kernel.org/doc/Documentation/x86/x86_64/mm.txt>):
///
/// | Start address       |  Offset  | End address         |  Size   | Description                 |
/// |---------------------|----------|---------------------|---------|-----------------------------|
/// | 0000_0000_0000_0000 |     0    | 0000_7FFF_FFFF_FFFF |  128 TB | User space                  |
/// | 0000_8000_0000_0000 |  +128 TB | FFFF_7FFF_FFFF_FFFF |   16 EB | Non-canonical addresses, up |
/// |                     |          |                     |         | to -128 TB                  |
/// | FFFF_8000_0000_0000 |  -128 TB | FFFF_87FF_FFFF_FFFF |    8 TB | ... unused hole             |
/// | FFFF_8800_0000_0000 |  -120 TB | FFFF_881F_FFFF_FFFF |  128 GB | direct mapping of all       |
/// |                     |          |                     |         | physical memory             |
/// | FFFF_8820_0000_0000 | ~-120 TB | FFFF_FFFF_7FFF_FFFF | ~120 TB | ... unused hole             |
/// | FFFF_FFFF_8000_0000 |    -2 GB | FFFF_FFFF_FFFF_FFFF |    2 GB | Kernel code                 |
pub fn initial_pml4(program_headers: &[ProgramHeader]) -> Result<PhysFrame, &'static str> {
    // Safety: this expects the frame allocator to be initialized and the memory
    // region it's handing memory out of to be identity mapped. This is true for
    // the lower 2 GiB after we boot. This reference will no longer be valid
    // after we reload the page tables!
    let pml4_frame: PhysFrame<Size4KiB> =
        FRAME_ALLOCATOR.lock().allocate_frame().ok_or("couldn't allocate a frame for PML4")?;
    let pml4 = unsafe { &mut *(pml4_frame.start_address().as_u64() as *mut PageTable) };
    pml4.zero();

    // Populate all the kernel space entries of the level 4 page table. This means
    // that these entries should never change, memory allocation will happen on
    // lower level page tables. This is done to permit the kernel to switch
    // between different level 4 page tables in the future. All page tables that
    // include these mappings will point to the same lower level page tables /
    // memory in kernel space.
    {
        let mut fa = FRAME_ALLOCATOR.lock();
        for entry in pml4.iter_mut().skip(256) {
            let pml3_frame: PhysFrame<Size4KiB> =
                fa.allocate_frame().ok_or("couldn't allocate a frame for PML3")?;
            let pml3 = unsafe { &mut *(pml3_frame.start_address().as_u64() as *mut PageTable) };
            pml3.zero();
            entry.set_frame(pml3_frame, PageTableFlags::PRESENT);
        }
    };

    let mut page_table = unsafe { OffsetPageTable::new(pml4, VirtAddr::new(0)) };

    // Safety: these operations are safe as they're not done on active page tables.
    unsafe {
        // Create a direct map for all physical memory, marking it NO_EXECUTE. The size
        // (128 GB) has been chosen go coincide with the amout of memory our
        // frame allocator can track.
        page_tables::create_offset_map(
            PhysFrame::<Size2MiB>::range(
                PhysFrame::from_start_address(PhysAddr::new(0x00_0000_0000)).unwrap(),
                PhysFrame::from_start_address(PhysAddr::new(0x20_0000_0000)).unwrap(),
            ),
            DIRECT_MAPPING_OFFSET,
            encryption_aware_page_table_flags(
                PageTableFlags::PRESENT
                    | PageTableFlags::GLOBAL
                    | PageTableFlags::WRITABLE
                    | PageTableFlags::NO_EXECUTE,
                PageAssignment::Private,
            ),
            &mut page_table,
        )
        .map_err(|_| "couldn't set up paging for physical memory")?;

        // Mapping for the kernel itself in the upper -2G of memory, based on the
        // mappings (and permissions) in the program header.
        page_tables::create_kernel_map(program_headers, &mut page_table)
            .map_err(|_| "couldn't set up paging for the kernel")?;
    }

    Ok(pml4_frame)
}

/// Allocates memory usable as a stack.
///
/// The stack will be one page (2 MiB) in size, will be allocated in the
/// VMA_ALLOCATOR area, and will consume two pages: one as a unmapped stack
/// guard (so that we'd get a page fault if we blow the stack), and one backed
/// by a physical frame as the actual stack.
///
/// The return address is usable as the stack pointer; that is, it points to the
/// end of the allocated stack page.
pub fn allocate_stack() -> VirtAddr {
    // Of the two pages we allocate, the first will be the stack guard page, and the
    // second will be the actual stack.
    let pages = VMA_ALLOCATOR
        .lock()
        .allocate(2)
        .expect("unable to allocate virtual memory for syscall stack");
    let frame = FRAME_ALLOCATOR
        .lock()
        .allocate_frame()
        .expect("unable to allocate physical memory for syscall stack");
    let stack_page = pages.start + 1;
    unsafe {
        PAGE_TABLES
            .lock()
            .get_mut()
            .unwrap()
            .map_to_with_table_flags(
                stack_page,
                frame,
                encryption_aware_page_table_flags(
                    PageTableFlags::GLOBAL
                        | PageTableFlags::PRESENT
                        | PageTableFlags::NO_EXECUTE
                        | PageTableFlags::WRITABLE,
                    PageAssignment::Private,
                ),
                encryption_aware_page_table_flags(
                    PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
                    PageAssignment::Private,
                ),
                FRAME_ALLOCATOR.lock().deref_mut(),
            )
            .expect("failed to update page tables for syscall stack")
            .flush();
    };

    (stack_page + 1).start_address()
}
