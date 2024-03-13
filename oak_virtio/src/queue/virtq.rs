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

use core::num::Wrapping;

use bitflags::bitflags;
use x86_64::PhysAddr;

bitflags! {
    /// Flags about a descriptor.
    ///
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-320005>.
    #[derive(Clone, Copy, Debug)]
    pub struct DescFlags: u16 {
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
pub struct Desc {
    /// The guest-physical address of the buffer.
    pub addr: PhysAddr,
    /// The lengths of the buffer.
    pub length: u32,
    /// Flags providing more info about this descriptor.
    pub flags: DescFlags,
    /// The index of the next descriptor in the chain if this is not the end
    /// (i.e. flags contain `DescFlags::VIRTQ_DESC_F_NEXT`), ignored
    /// otherwise.
    ///
    /// Not used for now, as we don't currently support chaining.
    pub next: u16,
}

impl Desc {
    pub fn new(flags: DescFlags, addr: PhysAddr, length: u32) -> Self {
        assert!(
            !flags.contains(DescFlags::VIRTQ_DESC_F_INDIRECT),
            "indirect descriptors not supported"
        );
        assert!(!flags.contains(DescFlags::VIRTQ_DESC_F_NEXT), "chained descriptors not supported");
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
    #[derive(Debug)]
    pub struct RingFlags: u16 {
        /// This indicates that the owner of the ring does not require queue notifications.
        const NO_NOTIFY = 1;
    }
}

/// The ring buffer that indicates which descriptors have been made available by
/// the driver.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-380006>.
#[repr(C, align(2))]
pub struct AvailRing<const QUEUE_SIZE: usize> {
    /// Driver-specific flags for the queue.
    pub flags: RingFlags,
    /// The next index that will be used in the ring (modulo `QUEUE_SIZE`).
    ///
    /// Starts at 0 and always increments. Must never be decremented. Wraps
    /// naturally when at the maximum `u16` value.
    pub idx: Wrapping<u16>,
    /// The ring-buffer containing indices of the heads of available descriptor
    /// chains.
    pub ring: [u16; QUEUE_SIZE],
    /// Event details. Only used if VIRTIO_F_EVENT_IDX has been negotiated,
    /// which we don't currently support. The field is only added to act as
    /// padding for now.
    pub used_event: u16,
}

impl<const QUEUE_SIZE: usize> Default for AvailRing<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            // We implement all drivers via polling, so don't want notifications.
            flags: RingFlags::NO_NOTIFY,
            idx: Wrapping(0),
            ring: [0; QUEUE_SIZE],
            used_event: 0,
        }
    }
}

/// The ring buffer that indicates which available descriptors have been
/// consumed by the device.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C, align(4))]
#[derive(Debug)]
pub struct UsedRing<const QUEUE_SIZE: usize> {
    /// Device-specific flags for the queue.
    pub flags: RingFlags,
    /// The next index that will be used in the ring (modulo `QUEUE_SIZE`).
    ///
    /// Starts at 0 and always increments. Must never be decremented. Wraps
    /// naturally when at the maximum `u16` value.
    pub idx: Wrapping<u16>,
    /// The ring-buffer containing the used elements.
    pub ring: [UsedElem; QUEUE_SIZE],
    /// Event details. Only used if VIRTIO_F_EVENT_IDX has been negotiated,
    /// which we don't currently support. The field is only added to act as
    /// padding for now.
    pub avail_event: u16,
}

impl<const QUEUE_SIZE: usize> Default for UsedRing<QUEUE_SIZE> {
    fn default() -> Self {
        Self {
            flags: RingFlags::empty(),
            idx: Wrapping(0),
            ring: [(); QUEUE_SIZE].map(|_| UsedElem::default()),
            avail_event: 0,
        }
    }
}

/// An element indicating a used descriptor chain.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-430008>.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct UsedElem {
    /// The index of the head of the used descriptor chain.
    pub id: u32,
    /// Total length of the bytes that was written to the used descriptor chain
    /// (only used for device-write-only descriptors).
    pub len: u32,
}

/// A split virtqueue implementation.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-240006>.
#[repr(C, align(64))]
pub struct VirtQueue<const QUEUE_SIZE: usize> {
    /// The descriptor table.
    pub desc: [Desc; QUEUE_SIZE],
    /// The available ring, which is controlled by the driver.
    pub avail: AvailRing<QUEUE_SIZE>,
    /// The used ring, which is controlled by the device.
    pub used: UsedRing<QUEUE_SIZE>,
}
