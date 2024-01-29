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

use alloc::{boxed::Box, collections::vec_deque::VecDeque, vec::Vec};
use core::{alloc::Allocator, num::Wrapping};

use virtq::{AvailRing, Desc, DescFlags, RingFlags, UsedElem, UsedRing, VirtQueue};
use x86_64::{PhysAddr, VirtAddr};

use crate::Translator;

pub mod virtq;

/// A queue where the descriptor buffers are only writable by the driver.
///
/// This is typically used for transmission queues.
pub struct DriverWriteOnlyQueue<'a, const QUEUE_SIZE: usize, const BUFFER_SIZE: usize, A: Allocator>
{
    /// The inner queue.
    pub inner: Queue<'a, QUEUE_SIZE, BUFFER_SIZE, A>,

    /// The indices of free descriptors that can be used by the driver for writing.
    free_ids: VecDeque<u16>,
}

impl<'a, const QUEUE_SIZE: usize, const BUFFER_SIZE: usize, A: Allocator>
    DriverWriteOnlyQueue<'a, QUEUE_SIZE, BUFFER_SIZE, A>
{
    pub fn new<VP: Translator>(translate: VP, alloc: &'a A) -> Self {
        let inner = Queue::new(DescFlags::empty(), translate, alloc);
        let mut free_ids = VecDeque::with_capacity(QUEUE_SIZE);

        // Add all the descriptors to the free list.
        for i in 0..QUEUE_SIZE as u16 {
            free_ids.push_back(i);
        }

        Self { inner, free_ids }
    }

    /// Writes the data to a buffer and adds its descriptor to the available ring if possible and
    /// returns the number of bytes that was copied from the `data` slice.
    ///
    /// If there are no free buffers (the device has not used any of the available buffers) we
    /// cannot write and have to wait.
    ///
    /// Note: we can only write data to a driver-write-only queue.
    pub fn write_buffer(&mut self, data: &[u8]) -> Option<usize> {
        // Add used buffers to free index queue.
        while let Some(element) = self.inner.get_next_used_element() {
            self.free_ids.push_back(element.id as u16)
        }

        let len = core::cmp::min(data.len(), BUFFER_SIZE);

        let id = self.free_ids.pop_back()?;
        // TODO(#2876): Avoid copying the buffer slice if possible.
        self.inner
            .get_mut_slice_from_index(id as usize, len)
            .copy_from_slice(&data[..len]);

        // Update the length of the descriptor.
        let desc = &mut self.inner.virt_queue.desc[id as usize];
        desc.length = len as u32;

        self.inner.add_available_descriptor(id);

        Some(len)
    }
}

/// A queue where the descriptor buffers are only writable by the device.
///
/// This is typically used for receiver queues.
pub struct DeviceWriteOnlyQueue<'a, const QUEUE_SIZE: usize, const BUFFER_SIZE: usize, A: Allocator>
{
    /// The inner queue.
    pub inner: Queue<'a, QUEUE_SIZE, BUFFER_SIZE, A>,
}

impl<'a, const QUEUE_SIZE: usize, const BUFFER_SIZE: usize, A: Allocator>
    DeviceWriteOnlyQueue<'a, QUEUE_SIZE, BUFFER_SIZE, A>
{
    pub fn new<VP: Translator>(translate: VP, alloc: &'a A) -> Self {
        let mut inner = Queue::new(DescFlags::VIRTQ_DESC_F_WRITE, translate, alloc);

        // Add all the descriptors to the available ring.
        for i in 0..QUEUE_SIZE as u16 {
            inner.add_available_descriptor(i);
        }

        Self { inner }
    }

    /// Reads the contents of the next used buffer from the queue, if one is avaialble.
    ///
    /// If a used buffer is found, this also advances the last used index by one.
    ///
    /// Note: we can only read data from a device-write-only queue.
    pub fn read_next_used_buffer(&mut self) -> Option<Vec<u8>> {
        let UsedElem { id, len } = self.inner.get_next_used_element()?;
        // TODO(#2876): Avoid copying the buffer slice if possible.
        let result = self
            .inner
            .get_mut_slice_from_index(id as usize, len as usize)
            .to_vec();

        // Recycle used element to so the buffer is available again.
        self.inner.add_available_descriptor(id as u16);

        Some(result)
    }
}

/// A container for a boxed virtqueue and its associated buffers.
pub struct Queue<'a, const QUEUE_SIZE: usize, const BUFFER_SIZE: usize, A: Allocator> {
    /// The underlying virtqueue.
    virt_queue: Box<VirtQueue<QUEUE_SIZE>, &'a A>,

    /// The global buffer used by the virtqueue. Each descriptor uses a slice with an offset into
    /// this single buffer for it own buffer.
    buffer: Vec<u8, &'a A>,

    /// The address of the first byte in the global buffer.
    base_offset: PhysAddr,

    /// The last index that was used when popping elements from the used ring.
    last_used_idx: Wrapping<u16>,
}

impl<'a, const QUEUE_SIZE: usize, const BUFFER_SIZE: usize, A: Allocator>
    Queue<'a, QUEUE_SIZE, BUFFER_SIZE, A>
{
    /// Creates a new instance of `Queue` by pre-initialising all the descriptors and creating
    /// enough buffer space for each descriptor.
    fn new<VP: Translator>(flags: DescFlags, translate: VP, alloc: &'a A) -> Self {
        assert!(
            QUEUE_SIZE.is_power_of_two(),
            "queue size must be a power of 2"
        );

        let mut buffer = Vec::with_capacity_in(BUFFER_SIZE * QUEUE_SIZE, alloc);
        buffer.resize(BUFFER_SIZE * QUEUE_SIZE, 0u8);
        let base_offset = translate(VirtAddr::from_ptr(buffer.as_ptr())).unwrap();
        let desc: Vec<Desc> = (0..QUEUE_SIZE)
            .map(|i| {
                Desc::new(
                    flags,
                    base_offset + (i * BUFFER_SIZE) as u64,
                    BUFFER_SIZE as u32,
                )
            })
            .collect();
        let desc: [Desc; QUEUE_SIZE] = desc.try_into().unwrap();
        let virt_queue = Box::new_in(
            VirtQueue {
                desc,
                avail: AvailRing::<QUEUE_SIZE>::default(),
                used: UsedRing::<QUEUE_SIZE>::default(),
            },
            alloc,
        );
        Self {
            virt_queue,
            buffer,
            base_offset,
            last_used_idx: Wrapping(0),
        }
    }

    /// Gets the address of the descriptor table.
    pub fn get_desc_addr(&self) -> VirtAddr {
        VirtAddr::from_ptr(self.virt_queue.desc.as_ptr())
    }

    /// Gets the address of the available ring.
    pub fn get_avail_addr(&self) -> VirtAddr {
        VirtAddr::from_ptr(&self.virt_queue.avail as *const _)
    }

    /// Gets the address of the used ring.
    pub fn get_used_addr(&self) -> VirtAddr {
        VirtAddr::from_ptr(&self.virt_queue.used as *const _)
    }

    /// Checks whether the device wants to be notified of queue changes.
    pub fn must_notify_device(&self) -> bool {
        // Memory fence so that we read a fresh value from the device-owned section.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);
        !self.virt_queue.used.flags.contains(RingFlags::NO_NOTIFY)
    }

    /// Gets a mutable slice into the buffer based on the index and length.
    fn get_mut_slice_from_index(&mut self, index: usize, len: usize) -> &mut [u8] {
        let start = (self.virt_queue.desc[index].addr - self.base_offset) as usize;
        let end = start + len;
        &mut self.buffer[start..end]
    }

    /// Tries to get the element referencing the next used descriptor that we have not yet seen, if
    /// any.
    ///
    /// If an unseen used descriptor is found, this also advances the last used index by one.
    fn get_next_used_element(&mut self) -> Option<UsedElem> {
        // Memory fence so that we read a fresh value from the device-owned section.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);
        let next_used = self.last_used_idx;
        if next_used == self.virt_queue.used.idx {
            None
        } else {
            self.last_used_idx += 1;
            Some(self.virt_queue.used.ring[next_used.0 as usize % QUEUE_SIZE])
        }
    }

    /// Adds a descriptor to the available ring.
    fn add_available_descriptor(&mut self, index: u16) {
        // Add the descriptor index to the available ring at the next location.
        self.virt_queue.avail.ring[self.virt_queue.avail.idx.0 as usize % QUEUE_SIZE] = index;
        // Increment the available ring index to use next time.
        let next = self.virt_queue.avail.idx + Wrapping(1);
        let idx = &mut self.virt_queue.avail.idx;
        // Memory fence to ensure the device will not see the index update before the available ring
        // entry update.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Release);
        *idx = next;
    }
}

#[cfg(test)]
mod tests;
