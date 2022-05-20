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
    ///
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-320005>.
    struct DescFlags: u16 {
        /// This marks a buffer as continuing via the next field to chain descriptors together.
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
    /// Flags providing more info about this descriptor.
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
    /// Flags about the available and used rings.
    struct RingFlags: u16 {
        /// This indicates that the owner of the ring does not require queue notifications.
        const NO_NOTIFY = 1;
    }
}

/// The ring buffer that indicates which descriptors have been made available by the driver.
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

/// The ring buffer that indicates which available descriptors have been consumed by the device.
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

/// An element indicating a used descriptor chain.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct UsedElem {
    /// The index of the head of the used descriptor chain.
    id: u32,
    /// Total length of the bytes that was written to the used descriptor chain (only used for
    /// device-write-only descriptors).
    len: u32,
}

/// A split virtqueue implementation.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-240006>.
#[repr(C, align(64))]
struct VirtQueue<const QUEUE_SIZE: usize> {
    /// The descriptor table.
    desc: [Desc; QUEUE_SIZE],
    /// The available ring, which is controlled by the driver.
    avail: AvailRing<QUEUE_SIZE>,
    /// The used ring, which is controlled by the device.
    used: UsedRing<QUEUE_SIZE>,
}

/// The intended use for the queue.
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

    /// The global buffer used by the virtqueue. Each descriptor uses a slice with an offset into
    /// this single buffer for it own buffer.
    ///
    /// We store it as a `Vec` on the global heap for now, but in future we would have a dedicated
    /// allocator to ensure it is located in memory pages that are shared with the host.
    buffer: Vec<u8>,

    /// The address of the first byte in the global buffer.
    base_offset: u64,

    /// The last index that was used when popping elements from the used ring.
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

    /// Creates a new instance of `Queue` by pre-initialising all the descriptors and creating
    /// enough buffer space for each descriptor.
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

    /// Checks whether the device wants to be notified of queue changes.
    pub fn must_notify_device(&self) -> bool {
        // Memory fence so that we read a fresh value from the device-owned section.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);
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
        if let Some(UsedElem { id, len }) = self.get_next_used_element() {
            // TODO(#2876): Avoid copying the buffer slice if possible.
            let result = self
                .get_mut_slice_from_index(id as usize, len as usize)
                .to_vec();

            // Recycle used element to so the buffer is available again.
            self.add_available_descriptor(id as u16);

            Some(result)
        } else {
            None
        }
    }

    /// Writes the data to a buffer and adds its descriptor to the available ring if possible and
    /// returns the number of bytes that was copied from the `data` slice.
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
                .copy_from_slice(&data[..len]);

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
        let next_used = self.last_used_idx;
        if next_used == self.virt_queue.used.idx {
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
        let next = self.virt_queue.avail.idx + 1;
        let idx = &mut self.virt_queue.avail.idx;
        // Memory fence to ensure the device will not see the index update before the available ring
        // entry update.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Release);
        *idx = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const QUEUE_SIZE: usize = 4;
    const BUFFER_SIZE: usize = 4;

    #[test]
    fn test_read_empty_queue() {
        let mut queue = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_device_write_only();
        let data = queue.read_next_used_buffer();
        assert!(data.is_none());
        assert_eq!(queue.last_used_idx, 0);
        assert_eq!(queue.virt_queue.used.idx, 0);
        assert_eq!(queue.virt_queue.avail.idx as usize, QUEUE_SIZE);
    }

    #[test]
    #[should_panic]
    fn test_read_from_driver_write_only_queue() {
        Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_driver_write_only().read_next_used_buffer();
    }

    #[test]
    #[should_panic]
    fn test_write_to_device_write_only_queue() {
        Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_device_write_only().write_buffer(&vec![0, 1]);
    }

    #[test]
    #[should_panic]
    fn test_invalid_queue_size() {
        // `QUEUE_SIZE` must be a power of 2.
        let _ = Queue::<3, BUFFER_SIZE>::new_device_write_only();
    }

    #[test]
    fn test_read_once() {
        let data = vec![0, 1, 2];
        let mut queue = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_device_write_only();

        let result = device_write(queue.virt_queue.as_mut(), &data);
        assert_eq!(Some(3), result);
        assert_eq!(queue.last_used_idx, 0);
        assert_eq!(queue.virt_queue.used.idx, 1);
        assert_eq!(queue.virt_queue.used.ring[0].len, 3);
        assert_eq!(queue.virt_queue.avail.idx as usize, QUEUE_SIZE);

        let read = queue.read_next_used_buffer();
        assert_eq!(queue.last_used_idx, 1);
        assert_eq!(Some(data), read);
        assert_eq!(queue.virt_queue.avail.idx as usize, QUEUE_SIZE + 1);
    }

    #[test]
    fn test_write_once() {
        let data = vec![0, 1, 2];
        let mut queue = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_driver_write_only();

        let result = queue.write_buffer(&data);
        assert_eq!(Some(3), result);
        assert_eq!(queue.virt_queue.avail.idx as usize, 1);

        let read = device_read_once(queue.virt_queue.as_mut());
        assert_eq!(queue.virt_queue.used.idx, 1);
        assert_eq!(Some(data), read);
    }

    #[test]
    fn test_write_too_long() {
        let data = vec![0, 1, 2, 3, 4];
        let mut queue = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_driver_write_only();

        let result = queue.write_buffer(&data);
        assert_eq!(Some(4), result);
    }

    #[test]
    fn test_device_queue_exhaustion() {
        let mut queue = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_device_write_only();
        let data = Some(vec![0]);
        // We can write 4 times.
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        // The 5th time should not write.
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(None, result);
        // Read twice to make space.
        let result = queue.read_next_used_buffer();
        assert_eq!(data, result);
        let result = queue.read_next_used_buffer();
        assert_eq!(data, result);
        // Now we can write twice.
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        // But the 3rd time should be blocked again.
        let result = device_write(queue.virt_queue.as_mut(), data.as_ref().unwrap());
        assert_eq!(None, result);
    }

    #[test]
    fn test_driver_queue_exhaustion() {
        let mut queue = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_driver_write_only();
        let data = Some(vec![0]);
        // We should be able to write 4 times.
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        // The 5th time should not be able to write.
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(None, result);
        // Read twice from the device.
        let result = device_read_once(queue.virt_queue.as_mut());
        assert_eq!(data, result);
        let result = device_read_once(queue.virt_queue.as_mut());
        assert_eq!(data, result);
        // Now we can write twice again.
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(Some(1), result);
        // But the 3rd time should be blocked again.
        let result = queue.write_buffer(data.as_ref().unwrap());
        assert_eq!(None, result);
    }

    #[test]
    fn test_many_echos() {
        let data_1 = Some(vec![0]);
        let data_2 = Some(vec![1, 2, 3]);
        let data_3 = Some(vec![4, 5]);
        let mut tx = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_driver_write_only();
        let mut rx = Queue::<QUEUE_SIZE, BUFFER_SIZE>::new_device_write_only();
        for _ in 0..100 {
            // Run batches of 3 echos or different data lengths repeatedly.
            tx.write_buffer(data_1.as_ref().unwrap()).unwrap();
            tx.write_buffer(data_2.as_ref().unwrap()).unwrap();
            tx.write_buffer(data_3.as_ref().unwrap()).unwrap();

            for _ in 0..3 {
                let tmp = device_read_once(tx.virt_queue.as_mut()).unwrap();
                device_write(rx.virt_queue.as_mut(), &tmp).unwrap();
            }

            let result = rx.read_next_used_buffer();
            assert_eq!(data_1, result);
            let result = rx.read_next_used_buffer();
            assert_eq!(data_2, result);
            let result = rx.read_next_used_buffer();
            assert_eq!(data_3, result);
        }
    }

    fn device_read_once<const QUEUE_SIZE: usize>(
        virt_queue: &mut VirtQueue<QUEUE_SIZE>,
    ) -> Option<Vec<u8>> {
        if virt_queue.avail.idx == virt_queue.used.idx {
            return None;
        }

        let ring_index = virt_queue.used.idx as usize % QUEUE_SIZE;
        let index = virt_queue.avail.ring[ring_index];
        let desc = &virt_queue.desc[index as usize];
        assert!(!desc.flags.contains(DescFlags::VIRTQ_DESC_F_WRITE));
        let used_elem = &mut virt_queue.used.ring[ring_index];
        used_elem.id = index as u32;
        used_elem.len = 0;
        virt_queue.used.idx += 1;
        // Safety: we purposely use unsafe code to simulate the way the the device/VMM will interact
        // with the memory. We treat the contents of the slice as data only and ensure we only pass
        // valid addresses and sizes from the tests.
        let buffer = unsafe {
            let ptr = desc.addr as usize as *const u8;
            let len = desc.length as usize;
            alloc::slice::from_raw_parts(ptr, len)
        };
        Some(buffer.to_vec())
    }

    fn device_write<const QUEUE_SIZE: usize>(
        virt_queue: &mut VirtQueue<QUEUE_SIZE>,
        data: &[u8],
    ) -> Option<usize> {
        if virt_queue.avail.idx == virt_queue.used.idx {
            return None;
        }

        let len = core::cmp::min(data.len(), BUFFER_SIZE);
        let ring_index = virt_queue.used.idx as usize % QUEUE_SIZE;
        let index = virt_queue.avail.ring[ring_index];
        let desc = &virt_queue.desc[index as usize];
        assert!(desc.flags.contains(DescFlags::VIRTQ_DESC_F_WRITE));
        let used_elem = &mut virt_queue.used.ring[ring_index];
        used_elem.id = index as u32;
        used_elem.len = len as u32;
        virt_queue.used.idx += 1;
        // Safety: we purposely use unsafe code to simulate the way the the device/VMM will interact
        // with the memory. We treat the contents of the slice as data only and ensure we only pass
        // valid addresses and lengths from the tests.
        let buffer = unsafe {
            let ptr = desc.addr as usize as *mut u8;
            alloc::slice::from_raw_parts_mut(ptr, len)
        };
        buffer.copy_from_slice(data);
        Some(len)
    }
}
