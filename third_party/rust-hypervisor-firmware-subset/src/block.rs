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

use core::cell::RefCell;

use crate::virtio::{Error as VirtioError, VirtioTransport};

const QUEUE_SIZE: usize = 16;

#[repr(C)]
#[repr(align(16))]
#[derive(Default)]
/// A virtio qeueue entry descriptor
struct Desc {
    addr: u64,
    length: u32,
    flags: u16,
    next: u16,
}

#[repr(C)]
#[repr(align(2))]
#[derive(Default)]
/// The virtio available ring
struct AvailRing {
    flags: u16,
    idx: u16,
    ring: [u16; QUEUE_SIZE],
}

#[repr(C)]
#[repr(align(4))]
#[derive(Default)]
/// The virtio used ring
struct UsedRing {
    flags: u16,
    idx: u16,
    ring: [UsedElem; QUEUE_SIZE],
}

#[repr(C)]
#[derive(Default)]
/// A single element in the used ring
struct UsedElem {
    id: u32,
    len: u32,
}

#[repr(C)]
#[repr(align(64))]
/// Device driver for virtio block over any transport
pub struct VirtioBlockDevice<'a> {
    transport: &'a mut dyn VirtioTransport,
    state: RefCell<DriverState>,
}

#[repr(C)]
#[repr(align(64))]
#[derive(Default)]
struct DriverState {
    descriptors: [Desc; QUEUE_SIZE],
    avail: AvailRing,
    used: UsedRing,
    next_head: usize,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    BlockIOError,

    BlockNotSupported,
}

#[repr(C)]
/// Header used for virtio block requests
struct BlockRequestHeader {
    request: u32,
    reserved: u32,
    sector: u64,
}

#[repr(C)]
/// Footer used for virtio block requests
struct BlockRequestFooter {
    status: u8,
}

pub trait SectorRead {
    /// Read a single sector (512 bytes) from the block device. `data` must be
    /// exactly 512 bytes long.
    fn read(&self, sector: u64, data: &mut [u8]) -> Result<(), Error>;
}

pub trait SectorWrite {
    /// Write a single sector (512 bytes) from the block device. `data` must be
    /// exactly 512 bytes long.
    fn write(&self, sector: u64, data: &mut [u8]) -> Result<(), Error>;
    fn flush(&self) -> Result<(), Error>;
}

#[derive(PartialEq, Copy, Clone)]
enum RequestType {
    Read = 0,
    Write = 1,
    Flush = 4,
}

impl<'a> VirtioBlockDevice<'a> {
    pub fn new(transport: &'a mut dyn VirtioTransport) -> VirtioBlockDevice<'a> {
        VirtioBlockDevice {
            transport,
            state: RefCell::new(DriverState::default()),
        }
    }

    pub fn init(&mut self) -> Result<(), VirtioError> {
        const VIRTIO_SUBSYSTEM_BLOCK: u32 = 0x2;
        const VIRTIO_F_VERSION_1: u64 = 1 << 32;

        const VIRTIO_STATUS_RESET: u32 = 0;
        const VIRTIO_STATUS_ACKNOWLEDGE: u32 = 1;
        const VIRTIO_STATUS_DRIVER: u32 = 2;
        const VIRTIO_STATUS_FEATURES_OK: u32 = 8;
        const VIRTIO_STATUS_DRIVER_OK: u32 = 4;
        const VIRTIO_STATUS_FAILED: u32 = 128;

        // Initialise the transport
        self.transport.init(VIRTIO_SUBSYSTEM_BLOCK)?;

        // Reset device
        self.transport.set_status(VIRTIO_STATUS_RESET);

        // Acknowledge
        self.transport.add_status(VIRTIO_STATUS_ACKNOWLEDGE);

        // And advertise driver
        self.transport.add_status(VIRTIO_STATUS_DRIVER);

        // Request device features
        let device_features = self.transport.get_features();

        if device_features & VIRTIO_F_VERSION_1 != VIRTIO_F_VERSION_1 {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::LegacyOnly);
        }

        // Don't support any advanced features for now
        let supported_features = VIRTIO_F_VERSION_1;

        // Report driver features
        self.transport
            .set_features(device_features & supported_features);

        self.transport.add_status(VIRTIO_STATUS_FEATURES_OK);
        if self.transport.get_status() & VIRTIO_STATUS_FEATURES_OK != VIRTIO_STATUS_FEATURES_OK {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::FeatureNegotiationFailed);
        }

        // Program queues
        self.transport.set_queue(0);

        let max_queue = self.transport.get_queue_max_size();

        // Hardcoded queue size to QUEUE_SIZE at the moment
        if max_queue < QUEUE_SIZE as u16 {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::QueueTooSmall);
        }
        self.transport.set_queue_size(QUEUE_SIZE as u16);

        // Update all queue parts
        let state = self.state.borrow_mut();
        let addr = state.descriptors.as_ptr() as u64;
        self.transport.set_descriptors_address(addr);

        let addr = (&state.avail as *const _) as u64;
        self.transport.set_avail_ring(addr);

        let addr = (&state.used as *const _) as u64;
        self.transport.set_used_ring(addr);

        // Confirm queue
        self.transport.set_queue_enable();

        // Report driver ready
        self.transport.add_status(VIRTIO_STATUS_DRIVER_OK);

        Ok(())
    }

    // Number of sectors that this device holds
    pub fn get_capacity(&self) -> u64 {
        u64::from(self.transport.read_device_config(0))
            | u64::from(self.transport.read_device_config(4)) << 32
    }

    fn request(
        &self,
        sector: u64,
        data: Option<&mut [u8]>,
        request: RequestType,
    ) -> Result<(), Error> {
        if request != RequestType::Flush {
            assert_eq!(512, data.as_ref().unwrap().len());
        }

        const VIRTQ_DESC_F_NEXT: u16 = 1;
        const VIRTQ_DESC_F_WRITE: u16 = 2;

        const VIRTIO_BLK_S_OK: u8 = 0;
        const VIRTIO_BLK_S_IOERR: u8 = 1;
        const VIRTIO_BLK_S_UNSUPP: u8 = 2;

        let header = BlockRequestHeader {
            request: request as u32,
            reserved: 0,
            sector,
        };

        let footer = BlockRequestFooter { status: 0 };

        let mut state = self.state.borrow_mut();

        let next_head = state.next_head;
        let mut d = &mut state.descriptors[next_head];
        let next_desc = (next_head + 1) % QUEUE_SIZE;
        d.addr = (&header as *const _) as u64;
        d.length = core::mem::size_of::<BlockRequestHeader>() as u32;
        d.flags = VIRTQ_DESC_F_NEXT;
        d.next = next_desc as u16;

        let mut d = &mut state.descriptors[next_desc];
        let next_desc = (next_desc + 1) % QUEUE_SIZE;
        if request != RequestType::Flush {
            d.addr = data.unwrap().as_ptr() as u64;
            d.length = core::mem::size_of::<[u8; 512]>() as u32;
        }

        d.flags = VIRTQ_DESC_F_NEXT
            | if request == RequestType::Read {
                VIRTQ_DESC_F_WRITE
            } else {
                0
            };
        d.next = next_desc as u16;

        let mut d = &mut state.descriptors[next_desc];
        d.addr = (&footer as *const _) as u64;
        d.length = core::mem::size_of::<BlockRequestFooter>() as u32;
        d.flags = VIRTQ_DESC_F_WRITE;
        d.next = 0;

        // Update ring to point to head of chain. Fence. Then update idx
        let avail_index = state.avail.idx;
        state.avail.ring[(avail_index % QUEUE_SIZE as u16) as usize] = state.next_head as u16;
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);

        state.avail.idx = state.avail.idx.wrapping_add(1);

        // Next free descriptor to use
        state.next_head = (next_desc + 1) % QUEUE_SIZE;

        // Notify queue has been updated
        self.transport.notify_queue(0);

        // Check for the completion of the request
        while unsafe { core::ptr::read_volatile(&state.used.idx) } != state.avail.idx {
            core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);
        }

        match footer.status {
            VIRTIO_BLK_S_OK => Ok(()),
            VIRTIO_BLK_S_IOERR => Err(Error::BlockIOError),
            VIRTIO_BLK_S_UNSUPP => Err(Error::BlockNotSupported),
            _ => Err(Error::BlockNotSupported),
        }
    }
}

impl<'a> SectorRead for VirtioBlockDevice<'a> {
    fn read(&self, sector: u64, data: &mut [u8]) -> Result<(), Error> {
        self.request(sector, Some(data), RequestType::Read)
    }
}

impl<'a> SectorWrite for VirtioBlockDevice<'a> {
    fn write(&self, sector: u64, data: &mut [u8]) -> Result<(), Error> {
        self.request(sector, Some(data), RequestType::Write)
    }

    fn flush(&self) -> Result<(), Error> {
        self.request(0, None, RequestType::Flush)
    }
}
