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

use alloc::vec::Vec;
use core::{
    alloc::{GlobalAlloc, Layout},
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use linked_list_allocator::{Heap, LockedHeap};
use log::info;
use oak_hal::{PageAssignment, Platform};
use spinning_top::Spinlock;
use x86_64::{
    PhysAddr, VirtAddr,
    structures::paging::{
        FrameAllocator, Page, PageSize, PageTableFlags, PhysFrame, Size2MiB, Size4KiB,
        mapper::{FlagUpdateError, Mapper},
        page::PageRange,
    },
};
use zerocopy::FromBytes;
use zeroize::Zeroize;

use crate::{
    FRAME_ALLOCATOR, PAGE_TABLES,
    mm::{Translator, encryption_aware_page_table_flags},
};

#[cfg(not(test))]
#[global_allocator]
static ALLOCATOR: LockedGrowableHeap = LockedGrowableHeap::empty();

#[cfg(test)]
static ALLOCATOR: LockedGrowableHeap = LockedGrowableHeap::empty();

/// Heap allocator that requests more physical memory as required.
struct GrowableHeap {
    /// Underlying heap allocator implementation.
    heap: Heap,

    /// Virtual address range available for the heap.
    base: Page<Size2MiB>,

    /// Non-inclusive limit of the heap: the last page of the heap.
    ///
    /// The heap will use [base, cursor) addresses in the virtual memory.
    available: PageRange<Size2MiB>,
}

impl GrowableHeap {
    pub const fn empty() -> Self {
        // Safety: zero is definitely aligned with a 2 MiB boundary.
        let zero_page = unsafe { Page::from_start_address_unchecked(VirtAddr::zero()) };
        Self { heap: Heap::empty(), base: zero_page, available: Page::range(zero_page, zero_page) }
    }

    /// Extends the current pool of memory by one 2 MiB page.
    fn extend(&mut self) -> Result<(), &'static str> {
        // We might want to do something more clever here, such as exponentially
        // increasing the number of frames we allocate. For now, let's just keep
        // extending by one frame.
        let frame: PhysFrame<Size2MiB> = FRAME_ALLOCATOR
            .lock()
            .allocate_frame()
            .ok_or("failed to allocate memory for kernel heap")?;
        let mut pt_guard = PAGE_TABLES.lock();
        let mapper = pt_guard.get_mut().unwrap();

        // Safety: if the page is already mapped, then we'll get an error and thus we
        // won't overwrite any existing mappings, Otherwise, creating a new
        // mapping is safe as the memory is currently unused and thus there
        // should be no references to that memory.
        unsafe {
            mapper
                .map_to_with_table_flags(
                    self.available.next().ok_or("kernel heap exhausted")?,
                    frame,
                    encryption_aware_page_table_flags(
                        PageTableFlags::PRESENT
                            | PageTableFlags::WRITABLE
                            | PageTableFlags::GLOBAL
                            | PageTableFlags::NO_EXECUTE
                            | PageTableFlags::HUGE_PAGE,
                        PageAssignment::Private,
                    ),
                    encryption_aware_page_table_flags(
                        PageTableFlags::PRESENT
                            | PageTableFlags::WRITABLE
                            | PageTableFlags::NO_EXECUTE,
                        PageAssignment::Private,
                    ),
                    FRAME_ALLOCATOR.lock().deref_mut(),
                )
                .map_err(|_| "unable to create page mapping for kernel heap")?
                .flush();
        }

        log::debug!(
            "Extending kernel heap to [{:#018x}..{:#018x}).",
            self.base.start_address().as_u64(),
            self.available.start.start_address().as_u64(),
        );
        Ok(())
    }

    pub unsafe fn init(&mut self, range: PageRange<Size2MiB>) {
        self.base = range.start;
        self.available = range;

        // Get the first 2 MiB of memory for the heap.
        self.extend().unwrap();

        unsafe {
            self.heap.init(self.base.start_address().as_mut_ptr(), Size2MiB::SIZE as usize);
        }
    }

    pub fn allocate_first_fit(&mut self, layout: Layout) -> Result<NonNull<u8>, ()> {
        // Try allocating the data structure; if the allocation fails, grow the heap and
        // try again until we succeed (or until we can't extend ourselves any
        // further)
        loop {
            match self.heap.allocate_first_fit(layout) {
                Ok(ptr) => return Ok(ptr),
                Err(()) => {
                    self.extend().map_err(|err| log::error!("{}", err))?;
                    // Safety: this is safe as we've just mapped a fresh 2 MiB page for the heap.
                    unsafe { self.heap.extend(Size2MiB::SIZE as usize) };
                }
            }
        }
    }

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: Layout) {
        unsafe {
            self.heap.deallocate(ptr, layout);
        }
    }
}

struct LockedGrowableHeap(Spinlock<GrowableHeap>);

impl LockedGrowableHeap {
    pub const fn empty() -> Self {
        Self(Spinlock::new(GrowableHeap::empty()))
    }
}

impl Deref for LockedGrowableHeap {
    type Target = Spinlock<GrowableHeap>;

    fn deref(&self) -> &Spinlock<GrowableHeap> {
        &self.0
    }
}

unsafe impl GlobalAlloc for LockedGrowableHeap {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        self.0
            .lock()
            .allocate_first_fit(layout)
            .ok()
            .map_or(core::ptr::null_mut(), |allocation| allocation.as_ptr())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        unsafe {
            self.0.lock().deallocate(NonNull::new_unchecked(ptr), layout);
        }
    }
}

/// Initializes the global allocator from the largest contiguous slice of
/// available memory.
///
/// Pointers to addresses in the memory area (or references to data contained
/// within the slice) must be considered invalid after calling this function, as
/// the allocator may overwrite the data at any point.
pub fn init_kernel_heap(range: PageRange<Size2MiB>) -> Result<(), &'static str> {
    // This is safe as we know the memory is available based on the e820 map.
    unsafe {
        ALLOCATOR.lock().init(range);
    }
    Ok(())
}

/// Sets up a heap of shared memory used for communication between the guest and
/// host.
pub fn init_guest_host_heap<P: Platform>() {
    // Allocate a section for guest-host communication (without the `ENCRYPTED` bit
    // set) We'll allocate 2*2MiB, as virtio needs more than 2 MiB for its data
    // structures.
    let guest_host_frames = FRAME_ALLOCATOR.lock().allocate_contiguous(2).unwrap();

    let guest_host_pages = {
        let pt_guard = PAGE_TABLES.lock();
        let pt = pt_guard.get().unwrap();
        Page::range(
            pt.translate_physical_frame(guest_host_frames.start).unwrap(),
            pt.translate_physical_frame(guest_host_frames.end).unwrap(),
        )
    };

    // Mark the guest-host pages as shared.
    let guest_host_frames_start =
        PhysFrame::<Size4KiB>::from_start_address(guest_host_frames.start.start_address())
            .expect("unaligned frame address");
    let guest_host_frames_end =
        PhysFrame::<Size4KiB>::from_start_address(guest_host_frames.end.start_address())
            .expect("unaligned frame address");
    for frame in PhysFrame::<Size4KiB>::range(guest_host_frames_start, guest_host_frames_end) {
        P::invalidate_frame(frame);
        P::change_frame_state(frame, PageAssignment::Shared);
    }

    // Safety: initializing the new heap is safe as the frame allocator guarantees
    // we're not overwriting any other memory; writing to the static mut is safe
    // as we're in the initialization code and thus there can be no concurrent
    // access.
    if crate::GUEST_HOST_HEAP
        .set(
            unsafe {
                init_guest_host_allocator(guest_host_pages, PAGE_TABLES.lock().get_mut().unwrap())
            }
            .unwrap(),
        )
        .is_err()
    {
        panic!("couldn't initialize the guest-host heap");
    }
}

/// Initializes an allocator for guest-host communication on unencrypted memory.
///
/// # Safety
///
/// The caller has to guarantee that the page range is valid and not in use, as
/// we will change page table flags for pages in that range.
unsafe fn init_guest_host_allocator<S: PageSize, M: Mapper<S>>(
    pages: PageRange<S>,
    mapper: &mut M,
) -> Result<LockedHeap, FlagUpdateError> {
    for page in pages {
        unsafe {
            mapper
                .update_flags(
                    page,
                    encryption_aware_page_table_flags(
                        PageTableFlags::PRESENT
                            | PageTableFlags::WRITABLE
                            | PageTableFlags::GLOBAL
                            | PageTableFlags::NO_EXECUTE,
                        PageAssignment::Shared,
                    ),
                )?
                .flush();
        }
    }

    info!(
        "Marking [{:#018x}..{:#018x}) for guest-host communication.",
        pages.start.start_address().as_u64(),
        pages.end.start_address().as_u64()
    );

    Ok(unsafe {
        LockedHeap::new(pages.start.start_address().as_mut_ptr(), pages.count() * S::SIZE as usize)
    })
}

pub struct SensitiveDiceDataMemory {
    start_ptr: *mut u8,
    eventlog_ptr: *mut u8,
    sensitive_memory_length: usize,
    #[allow(dead_code)]
    dice_attestation_ptr: Option<*mut u8>,
}

impl SensitiveDiceDataMemory {
    /// Safety: Caller must ensure that there is only instance of this
    /// struct.
    pub unsafe fn new(
        kernel_args: &crate::args::Args,
        info: &oak_linux_boot_params::BootParams,
    ) -> Self {
        let sensitive_memory_length = kernel_args
            .get(&alloc::format!("--{}", oak_dice::evidence::DICE_DATA_LENGTH_CMDLINE_PARAM))
            .map(|arg| {
                arg.parse::<usize>()
                    .expect("dice data length kernel arg could not be converted to usize")
            })
            .inspect(|&length| {
                assert!(
                    length >= core::mem::size_of::<oak_dice::evidence::Stage0DiceData>(),
                    "the cmdline argument for dice data length must be no less than the size of the Stage0DiceData struct"
                );
            })
            // Older versions of stage0 do not supply this argument. In this case we assume the
            // length of the dice data is the length of the associated struct.
            .unwrap_or_else(::core::mem::size_of::<oak_dice::evidence::Stage0DiceData>);

        let dice_data_phys_addr =
            fetch_address_from_cmdline(kernel_args, oak_dice::evidence::DICE_DATA_CMDLINE_PARAM);

        let eventlog_phys_addr =
            fetch_address_from_cmdline(kernel_args, oak_dice::evidence::EVENTLOG_CMDLINE_PARAM);
        let dice_data_attestation_addr = fetch_address_from_cmdline(
            kernel_args,
            oak_dice::evidence::DICE_DATA_ATTESTATION_PARAM,
        );

        let dice_data_phys_addr = dice_data_phys_addr
            .expect("stage 0 command line lacks required argument: dice data C-struct address");
        let eventlog_phys_addr = eventlog_phys_addr
            .expect("stage 0 command line lacks required argument: eventlog address");

        // Ensure that the dice data is stored within reserved memory.
        let end = dice_data_phys_addr + (sensitive_memory_length as u64 - 1);
        assert!(info.e820_table().iter().any(|entry| {
            let dice_data_fully_contained_in_segment = {
                let range = PhysAddr::new(entry.addr().try_into().unwrap())
                    ..=PhysAddr::new((entry.addr() + entry.size()).try_into().unwrap());
                range.contains(&dice_data_phys_addr)
                    && range.contains(&end)
                    && range.contains(&eventlog_phys_addr)
            };

            entry.entry_type().expect("failed to get type")
                == oak_linux_boot_params::E820EntryType::RESERVED
                && dice_data_fully_contained_in_segment
        }));

        let dice_data_virt_addr = fetch_virtual_address(&dice_data_phys_addr);
        let eventlog_virt_addr = fetch_virtual_address(&eventlog_phys_addr);

        // If the dice attester is passed to this layer, read it and pass it along to
        // the struct.
        // TODO: b/463325402 - Have the Oak Restricted Kernel depend on the dice
        // attester in the future instead of the event log and dice data C-struct.
        let dice_data_attestation_virt_addr =
            if let Some(dice_data_attestation_addr) = dice_data_attestation_addr {
                assert!(info.e820_table().iter().any(|entry| {
                    let range = PhysAddr::new(entry.addr().try_into().unwrap())
                        ..=PhysAddr::new((entry.addr() + entry.size()).try_into().unwrap());
                    range.contains(&dice_data_attestation_addr) && range.contains(&end)
                }));
                let dice_data_attestation_virt_address =
                    fetch_virtual_address(&dice_data_attestation_addr);

                Some(dice_data_attestation_virt_address.as_mut_ptr())
            } else {
                None
            };
        Self {
            start_ptr: dice_data_virt_addr.as_mut_ptr(),
            eventlog_ptr: eventlog_virt_addr.as_mut_ptr(),
            dice_attestation_ptr: dice_data_attestation_virt_addr,
            sensitive_memory_length,
        }
    }

    pub fn read_stage0_dice_data(&self) -> oak_dice::evidence::Stage0DiceData {
        let dice_memory_slice = unsafe {
            core::slice::from_raw_parts(
                self.start_ptr,
                core::mem::size_of::<oak_dice::evidence::Stage0DiceData>(),
            )
        };

        let dice_data = oak_dice::evidence::Stage0DiceData::read_from_bytes(dice_memory_slice)
            .expect("failed to read dice data");

        if dice_data.magic != oak_dice::evidence::STAGE0_MAGIC {
            panic!("dice data loaded from stage0 failed validation");
        }
        dice_data
    }

    pub fn read_encoded_eventlog(&self) -> Vec<u8> {
        // Read the event log size (first 8 bytes)
        let event_log_size = unsafe {
            let size_bytes = core::slice::from_raw_parts(self.eventlog_ptr, 8);
            u64::from_le_bytes(size_bytes.try_into().unwrap()) as usize
        };

        // Read the event log bytes
        let event_log_bytes =
            unsafe { core::slice::from_raw_parts(self.eventlog_ptr.add(8), event_log_size) };

        event_log_bytes.to_vec()
    }
}

impl Drop for SensitiveDiceDataMemory {
    fn drop(&mut self) {
        // Zero out the sensitive_dice_data_memory.
        // Safety: This struct is only used once. We have checked the length,
        // know it is backed by physical memory and is reserved.
        (unsafe { core::slice::from_raw_parts_mut(self.start_ptr, self.sensitive_memory_length) })
            .zeroize();
    }
}

// Fetches a physical address from a stage 0 kernel command line argument. If
// the argument is not present, None is returned. This function will panic in
// the event the argument is found and cannot be parsed.
fn fetch_address_from_cmdline(
    kernel_args: &crate::args::Args,
    stage0_arg: &str,
) -> Option<PhysAddr> {
    let arg = kernel_args.get(&alloc::format!("--{}", stage0_arg))?;
    let parsed_arg =
        u64::from_str_radix(arg.strip_prefix("0x").expect("failed stripping the hex prefix"), 16)
            .expect("couldn't parse address as a hex number");
    Some(PhysAddr::new(parsed_arg))
}

// Fetches the virtual address from the Page Tables using the provided physical
// address. The function panics if the Page Table cannot be fetched or if the
// virtual address cannot be fetched.
fn fetch_virtual_address(phys_address: &PhysAddr) -> VirtAddr {
    let pt_guard = PAGE_TABLES.lock();
    let pt = pt_guard.get().expect("failed to get page tables");
    pt.translate_physical(*phys_address).expect("failed to translate physical eventlog address")
}
