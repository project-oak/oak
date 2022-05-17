// Copyright © 2019 Intel Corporation
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
// Copyright 2022 The Project Oak Authors
// SPDX-License-Identifier: Apache-2.0
//

use core::cell::RefCell;

use crate::virtio::{Error as VirtioError, VirtioTransport};

/// A virtio qeueue entry descriptor.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-320005>.
#[repr(C)]
#[repr(align(16))]
#[derive(Default)]
struct Desc {
    addr: u64,
    length: u32,
    flags: u16,
    next: u16,
}

/// The virtio available ring.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-380006>.
#[repr(C)]
#[repr(align(2))]
struct AvailRing<const QUEUE_SIZE: usize> {
    flags: u16,
    idx: u16,
    ring: [u16; QUEUE_SIZE],
}

impl<const QUEUE_SIZE: usize> Default for AvailRing<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            flags: 0,
            idx: 0,
            ring: [0; QUEUE_SIZE],
        }
    }
}

/// The virtio used ring.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C)]
#[repr(align(4))]
struct UsedRing<const QUEUE_SIZE: usize> {
    flags: u16,
    idx: u16,
    ring: [UsedElem; QUEUE_SIZE],
}

impl<const QUEUE_SIZE: usize> Default for UsedRing<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            flags: 0,
            idx: 0,
            ring: [(); QUEUE_SIZE].map(|_| UsedElem::default()),
        }
    }
}

/// A single element in the used ring.
///
/// <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C)]
#[derive(Default)]
struct UsedElem {
    id: u32,
    len: u32,
}

#[repr(C)]
#[repr(align(64))]
struct Queue<const QUEUE_SIZE: usize> {
    descriptors: [Desc; QUEUE_SIZE],
    avail: AvailRing<QUEUE_SIZE>,
    used: UsedRing<QUEUE_SIZE>,
    next_head: usize,
}

impl<const QUEUE_SIZE: usize> Default for Queue<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            descriptors: [(); QUEUE_SIZE].map(|_| Desc::default()),
            avail: AvailRing::<QUEUE_SIZE>::default(),
            used: UsedRing::<QUEUE_SIZE>::default(),
            next_head: 0,
        }
    }
}

#[repr(C)]
#[repr(align(64))]
/// Device driver for virtio block over any transport
pub struct VirtioDevice<T: VirtioTransport, const QUEUE_SIZE: usize, const NUM_QUEUES: usize> {
    transport: T,
    queues: RefCell<[Queue<QUEUE_SIZE>; NUM_QUEUES]>,
}

impl<T, const QUEUE_SIZE: usize, const NUM_QUEUES: usize> VirtioDevice<T, QUEUE_SIZE, NUM_QUEUES>
where
    T: VirtioTransport,
{
    pub fn new(transport: T) -> Self {
        // Queue size must be a power of two for split virtqueues.
        // See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-240006>.
        assert!(QUEUE_SIZE.is_power_of_two());
        Self {
            transport,
            queues: RefCell::new([(); NUM_QUEUES].map(|_| Queue::default())),
        }
    }

    /// Initialises the device.
    ///
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-920001>.
    pub fn init(&mut self, device_type: u32) -> Result<(), VirtioError> {
        // Virtio Version 1 feature bit.
        // See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-4100006>.
        const VIRTIO_F_VERSION_1: u64 = 1 << 32;

        // Status fields.
        // See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-100001>.
        const VIRTIO_STATUS_RESET: u32 = 0;
        const VIRTIO_STATUS_ACKNOWLEDGE: u32 = 1;
        const VIRTIO_STATUS_DRIVER: u32 = 2;
        const VIRTIO_STATUS_FEATURES_OK: u32 = 8;
        const VIRTIO_STATUS_DRIVER_OK: u32 = 4;
        const VIRTIO_STATUS_FAILED: u32 = 128;

        // Initialise the transport.
        self.transport.init(device_type)?;

        // Reset device.
        self.transport.set_status(VIRTIO_STATUS_RESET);

        // Acknowledge.
        self.transport.add_status(VIRTIO_STATUS_ACKNOWLEDGE);

        // And advertise driver.
        self.transport.add_status(VIRTIO_STATUS_DRIVER);

        // Request device features.
        let device_features = self.transport.get_features();

        if device_features & VIRTIO_F_VERSION_1 != VIRTIO_F_VERSION_1 {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::LegacyOnly);
        }

        // Don't support any advanced features for now.
        let supported_features = VIRTIO_F_VERSION_1;

        // Report driver features.
        self.transport
            .set_features(device_features & supported_features);

        self.transport.add_status(VIRTIO_STATUS_FEATURES_OK);
        if self.transport.get_status() & VIRTIO_STATUS_FEATURES_OK != VIRTIO_STATUS_FEATURES_OK {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::FeatureNegotiationFailed);
        }

        // Program queues.
        for i in 0..NUM_QUEUES {
            self.transport.set_queue(i as u16);

            let max_queue = self.transport.get_queue_max_size();

            // Hardcoded queue size to QUEUE_SIZE at the moment.
            if max_queue < QUEUE_SIZE as u16 {
                self.transport.add_status(VIRTIO_STATUS_FAILED);
                return Err(VirtioError::QueueTooSmall);
            }
            self.transport.set_queue_size(QUEUE_SIZE as u16);

            let queue = &self.queues.borrow_mut()[i];
            // Update all queue parts.
            let addr = queue.descriptors.as_ptr() as u64;
            self.transport.set_descriptors_address(addr);

            let addr = (&queue.avail as *const _) as u64;
            self.transport.set_avail_ring(addr);

            let addr = (&queue.used as *const _) as u64;
            self.transport.set_used_ring(addr);

            // Confirm queue.
            self.transport.set_queue_enable();
        }

        // Report driver ready.
        self.transport.add_status(VIRTIO_STATUS_DRIVER_OK);

        Ok(())
    }

    // Reads 32 bits of a config value from the transport.
    pub fn get_config(&self, offset: u64) -> u32 {
        self.transport.read_device_config(offset)
    }
}
