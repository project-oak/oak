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

use alloc::{boxed::Box, collections::vec_deque::VecDeque, vec, vec::Vec};
use bitflags::bitflags;

bitflags! {
    /// Flags about a descriptor.
    struct DescFlags: u16 {
        /// This marks a buffer as continuing via the next field to chain descriptors togetehr.
        ///
        /// Not supported for now.
        const VIRTQ_DESC_F_NEXT = 1;
        /// This marks a buffer as device write-only (otherwise device read-only).
        const VIRTQ_DESC_F_WRITE = 2;
        /// This means the buffer contains a list of buffer descriptors.
        ///
        /// Not supported for now.
        const VIRTQ_DESC_F_INDIRECT = 4;
    }
}

/// A descriptor for a byte buffer used in a virtio queue.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-320005>.
#[repr(C, align(16))]
#[derive(Debug)]
struct Desc {
    /// The guest-physical address of the buffer.
    ///
    /// We use an identity mapping, so it is also the guest virtual address.
    addr: u64,
    /// The lengths of the buffer.
    length: u32,
    /// Flags about the buffer.
    flags: DescFlags,
    /// The index of the next descriptor in the chain if this is not the end (i.e. flags contain
    /// `DescFlags::VIRTQ_DESC_F_NEXT`), ignored otherwise.
    ///
    /// Not used for now, as we don't currently support chaining.
    next: u16,
}

impl Desc {
    fn new(flags: DescFlags, addr: u64, length: u32) -> Self {
        assert!(
            !flags.contains(DescFlags::VIRTQ_DESC_F_INDIRECT),
            "Indirect descriptors not supported."
        );
        assert!(
            !flags.contains(DescFlags::VIRTQ_DESC_F_NEXT),
            "Chained descriptors not supported."
        );
        Self {
            addr,
            length,
            flags,
            // For simplicity we don't set up descriptor chains.
            next: 0,
        }
    }
}

bitflags! {
    /// Flags about a the available or used rings.
    struct RingFlags: u16 {
        /// This indicates that the owner of the ring does not require queue notifications.
        const NO_NOTIFY = 1;
    }
}

/// The ring buffer that indicates which descriptors are available.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-380006>.
#[repr(C, align(2))]
struct AvailRing<const QUEUE_SIZE: usize> {
    /// Driver-specific flags for the queue.
    flags: RingFlags,
    /// The next index that will be used in the ring (modulo `QUEUE_SIZE`).
    ///
    /// Starts at 0 and always increments. Must never be decremented.
    idx: u16,
    /// The ring-buffer containing indices of the heads of available descriptor chains.
    ring: [u16; QUEUE_SIZE],
}

impl<const QUEUE_SIZE: usize> Default for AvailRing<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            // We implement all drivers via polling, so don't want notifications.
            flags: RingFlags::NO_NOTIFY,
            idx: 0,
            ring: [0; QUEUE_SIZE],
        }
    }
}

/// The ring buffer that indicates which descriptors have been used.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C, align(4))]
struct UsedRing<const QUEUE_SIZE: usize> {
    /// Device-specific flags for the queue.
    flags: RingFlags,
    /// The next index that will be used in the ring (modulo `QUEUE_SIZE`).
    ///
    /// Starts at 0 and always increments. Must never be decremented.
    idx: u16,
    /// The ring-buffer containing the used elements.
    ring: [UsedElem; QUEUE_SIZE],
}

impl<const QUEUE_SIZE: usize> Default for UsedRing<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            flags: RingFlags::empty(),
            idx: 0,
            ring: [(); QUEUE_SIZE].map(|_| UsedElem::default()),
        }
    }
}

/// An element indicating a used descriptor.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct UsedElem {
    /// The index of the head of the used descriptor chain.
    id: u32,
    /// Total length of the bytes that was written to the used descriptor chain for
    /// device-write-only descriptors.
    len: u32,
}

/// A split virtqueue implementation.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-240006>.
#[repr(C, align(64))]
struct VirtQueue<const QUEUE_SIZE: usize> {
    /// The descriptor table.
    desc: [Desc; QUEUE_SIZE],
    /// The available ring.
    avail: AvailRing<QUEUE_SIZE>,
    /// The used ring.
    used: UsedRing<QUEUE_SIZE>,
}

#[derive(PartialEq, Eq)]
enum QueueType {
    DeviceWriteOnly,
    DriverWriteOnly,
}

/// A container for a boxed virtqueue and its associated buffers.
pub struct Queue<const QUEUE_SIZE: usize, const BUFFER_SIZE: usize> {
    /// The type of queue (whether the device or the driver can write to the buffers).
    queue_type: QueueType,

    /// The underlying virtqueue.
    ///
    /// We store it on the global heap for now, but in future we would have a dedicated allocator
    /// to ensure it is in memory pages that are shared with the host.
    virt_queue: Box<VirtQueue<QUEUE_SIZE>>,

    /// The buffer used by the virtqueue. Each descriptor uses a slice with an offset into this
    /// single buffer.
    ///
    /// We store it as a `Vec` on the global heap for now, but in future we would have a dedicated
    /// allocator to ensure it is in memory pages that are shared with the host.
    buffer: Vec<u8>,

    /// The address of the first byte in the buffer.
    base_offset: u64,

    /// The last index we used while popping used items.
    last_used_idx: u16,

    /// The indices of free descriptors that can be used by the driver for writing.
    free_ids: VecDeque<u16>,
}

impl<const QUEUE_SIZE: usize, const BUFFER_SIZE: usize> Queue<QUEUE_SIZE, BUFFER_SIZE> {
    /// Creates a new queue where the descriptor buffers are only writable by the driver.
    ///
    /// This is typically used for transmission queues.
    pub fn new_driver_write_only() -> Self {
        let mut result = Self::new(QueueType::DriverWriteOnly);

        // Add all the descriptors to the free list.
        for i in 0..QUEUE_SIZE as u16 {
            result.free_ids.push_back(i);
        }

        result
    }

    /// Creates a new queue where the descriptor buffers are only writable by the device.
    ///
    /// This is typically used for receiver queues.
    pub fn new_device_write_only() -> Self {
        let mut result = Self::new(QueueType::DeviceWriteOnly);

        // Add all the descriptors to the available ring.
        for i in 0..QUEUE_SIZE as u16 {
            result.add_available_descriptor(i);
        }

        result
    }

    /// Creates a new instance of `Queue` by pre-initialising buffer space for each descriptor in a
    /// `Vec`.
    fn new(queue_type: QueueType) -> Self {
        assert!(
            QUEUE_SIZE.is_power_of_two(),
            "Queue size must be a power of 2."
        );
        let flags = match queue_type {
            QueueType::DeviceWriteOnly => DescFlags::VIRTQ_DESC_F_WRITE,
            QueueType::DriverWriteOnly => DescFlags::empty(),
        };

        let buffer = vec![0u8; BUFFER_SIZE * QUEUE_SIZE];
        let base_offset = buffer.as_ptr() as u64;
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
        let virt_queue = Box::new(VirtQueue {
            desc,
            avail: AvailRing::<QUEUE_SIZE>::default(),
            used: UsedRing::<QUEUE_SIZE>::default(),
        });
        Self {
            queue_type,
            virt_queue,
            buffer,
            base_offset,
            last_used_idx: 0,
            free_ids: VecDeque::with_capacity(QUEUE_SIZE),
        }
    }

    /// Gets the address of the descriptor table.
    pub fn get_desc_addr(&self) -> u64 {
        self.virt_queue.desc.as_ptr() as u64
    }

    /// Gets the address of the available ring.
    pub fn get_avail_addr(&self) -> u64 {
        (&self.virt_queue.avail as *const _) as u64
    }

    /// Gets the address of the used ring.
    pub fn get_used_addr(&self) -> u64 {
        (&self.virt_queue.used as *const _) as u64
    }

    /// Whether the device wants to be notified of queue changes.
    pub fn must_notify_device(&self) -> bool {
        !self.virt_queue.used.flags.contains(RingFlags::NO_NOTIFY)
    }

    /// Reads the contents of the next used buffer from the queue, if one is avaialble.
    ///
    /// If a used buffer is found, this also advances the last used index by one.
    ///
    /// Note: we can only read data from a device-write-only queue.
    pub fn read_next_used_buffer(&mut self) -> Option<Vec<u8>> {
        assert!(
            self.queue_type != QueueType::DriverWriteOnly,
            "Cannot read from a driver-write-only queue."
        );
        // TODO(#2876): Avoid copying the buffer slice if possible.
        self.get_next_used_element().map(|used_element| {
            self.get_mut_slice_from_index(used_element.id as usize, used_element.len as usize)
                .to_vec()
        })
    }

    /// Writes the data to a buffer and adds its descriptor to the available ring if possible and
    /// returns the number of bytes that was copied from the slice.
    ///
    /// If there are no free buffers (the device has not used any of the available buffers) we
    /// cannot write and have to wait.
    ///
    /// Note: we can only write data to a driver-write-only queue.
    pub fn write_buffer(&mut self, data: &[u8]) -> Option<usize> {
        assert!(
            self.queue_type != QueueType::DeviceWriteOnly,
            "Cannot write to a device-write-only queue."
        );
        // Add used buffers to free index queue.
        while let Some(element) = self.get_next_used_element() {
            self.free_ids.push_back(element.id as u16)
        }

        let len = core::cmp::min(data.len(), BUFFER_SIZE);

        if let Some(id) = self.free_ids.pop_back() {
            // TODO(#2876): Avoid copying the buffer slice if possible.
            self.get_mut_slice_from_index(id as usize, len)
                .copy_from_slice(data);

            // Update the length of the descriptor.
            let mut desc = &mut self.virt_queue.desc[id as usize];
            desc.length = len as u32;

            self.add_available_descriptor(id);

            Some(len)
        } else {
            None
        }
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
        let next_used = self.virt_queue.used.idx;
        if next_used == self.last_used_idx {
            None
        } else {
            self.last_used_idx += 1;
            Some(self.virt_queue.used.ring[next_used as usize % QUEUE_SIZE])
        }
    }

    /// Adds a descriptor to the available ring.
    fn add_available_descriptor(&mut self, index: u16) {
        // Add the descriptor index to the available ring at the next location.
        self.virt_queue.avail.ring[self.virt_queue.avail.idx as usize % QUEUE_SIZE] = index;
        // Increment the available ring index to use next time.
        self.virt_queue.avail.idx += 1;
    }
}
