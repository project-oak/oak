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

use crate::queue::virtq::{AvailRing, Desc, DescFlags, UsedElem, UsedRing};
use alloc::{collections::BTreeMap, vec::Vec};
use core::{
    cell::{Cell, RefCell},
    mem::size_of,
};
use rust_hypervisor_firmware_virtio::virtio::{Error, VirtioTransport};

/// A transport implementation that can be used for testing virtio device implementations.
///
/// Warning: we purposely use unsafe code to simulate the way the the device/VMM will interact with
/// the memory. Tests must ensure that valid memory and offset values are provided to avoid memory
/// safety issues.
#[derive(Default, Debug)]
pub struct TestingTransport {
    pub status: Cell<u32>,
    pub features: Cell<u64>,
    pub queue_num: Cell<u16>,
    pub max_queue_size: u16,
    pub queues: RefCell<BTreeMap<u16, QueueInfo>>,
    pub config: RefCell<BTreeMap<u64, u32>>,
}

#[derive(Default, Debug)]
pub struct QueueInfo {
    pub queue_size: u16,
    pub descriptor_address: u64,
    pub avail_ring: u64,
    pub used_ring: u64,
    pub enabled: bool,
    pub notified: bool,
}

impl TestingTransport {
    fn get_desc<const QUEUE_SIZE: usize>(&self, queue_num: u16, index: u16) -> &mut Desc {
        assert!((index as usize) < QUEUE_SIZE);
        let queue_info = self.queues.borrow().get(&queue_num).unwrap();
        let address = queue_info.descriptor_address as usize + index as usize * size_of::<Desc>();
        unsafe { &mut *(address as *mut Desc) }
    }

    fn get_avail_ring<const QUEUE_SIZE: usize>(&self, queue_num: u16) -> &AvailRing<QUEUE_SIZE> {
        let queue_info = self.queues.borrow().get(&queue_num).unwrap();
        let address = queue_info.avail_ring as usize;
        unsafe { &*(address as *mut AvailRing<QUEUE_SIZE>) }
    }

    fn get_used_ring<const QUEUE_SIZE: usize>(&self, queue_num: u16) -> &mut UsedRing<QUEUE_SIZE> {
        let queue_info = self.queues.borrow().get(&queue_num).unwrap();
        let address = queue_info.used_ring as usize;
        unsafe { &mut *(address as *mut UsedRing<QUEUE_SIZE>) }
    }

    pub fn device_read_once_from_queue<const QUEUE_SIZE: usize>(
        &self,
        queue_num: u16,
    ) -> Option<Vec<u8>> {
        let avail = self.get_avail_ring::<QUEUE_SIZE>(queue_num);
        let mut used = self.get_used_ring::<QUEUE_SIZE>(queue_num);
        if avail.idx == used.idx {
            return None;
        }

        let ring_index = used.idx.0 as usize % QUEUE_SIZE;
        let index = avail.ring[ring_index];
        let desc = self.get_desc::<QUEUE_SIZE>(queue_num, index);

        assert!(!desc.flags.contains(DescFlags::VIRTQ_DESC_F_WRITE));
        let used_elem = &mut used.ring[ring_index];
        used_elem.id = index as u32;
        used_elem.len = 0;
        used.idx += 1;
        let buffer = unsafe {
            let ptr = desc.addr as usize as *const u8;
            let len = desc.length as usize;
            alloc::slice::from_raw_parts(ptr, len)
        };
        Some(buffer.to_vec())
    }

    pub fn device_write_to_queue<const QUEUE_SIZE: usize>(
        &self,
        queue_num: u16,
        data: &[u8],
    ) -> Option<usize> {
        let avail = self.get_avail_ring::<QUEUE_SIZE>(queue_num);
        let used = self.get_used_ring::<QUEUE_SIZE>(queue_num);
        if avail.idx == used.idx {
            return None;
        }

        let ring_index = used.idx.0 as usize % QUEUE_SIZE;
        let index = avail.ring[ring_index];
        let desc = self.get_desc::<QUEUE_SIZE>(queue_num, index);
        let len = core::cmp::min(data.len(), desc.length as usize);
        assert!(desc.flags.contains(DescFlags::VIRTQ_DESC_F_WRITE));
        let used_elem = &mut used.ring[ring_index];
        used_elem.id = index as u32;
        used_elem.len = 0;
        used.idx += 1;
        let buffer = unsafe {
            let ptr = desc.addr as usize as *mut u8;
            alloc::slice::from_raw_parts_mut(ptr, len)
        };
        buffer.copy_from_slice(data);
        Some(len)
    }
}

impl VirtioTransport for TestingTransport {
    fn init(&mut self, _device_type: u32) -> Result<(), Error> {
        Ok(())
    }

    fn get_status(&self) -> u32 {
        self.status.get()
    }

    fn set_status(&self, status: u32) {
        self.status.set(status);
    }

    fn add_status(&self, status: u32) {
        self.status.set(self.status.get() | status);
    }

    fn reset(&self) {
        self.status.set(0);
    }

    fn get_features(&self) -> u64 {
        self.features.get()
    }

    fn set_features(&self, features: u64) {
        self.features.set(features);
    }

    fn set_queue(&self, queue: u16) {
        if !self.queues.borrow().contains_key(&queue) {
            self.queues.borrow_mut().insert(queue, QueueInfo::default());
        }
        self.queue_num.set(queue);
    }

    fn get_queue_max_size(&self) -> u16 {
        self.max_queue_size
    }

    fn set_queue_size(&self, queue_size: u16) {
        assert!(queue_size <= self.max_queue_size);
        self.queues
            .borrow_mut()
            .get_mut(&self.queue_num.get())
            .unwrap()
            .queue_size = queue_size;
    }

    fn set_descriptors_address(&self, address: u64) {
        self.queues
            .borrow_mut()
            .get_mut(&self.queue_num.get())
            .unwrap()
            .descriptor_address = address;
    }

    fn set_avail_ring(&self, address: u64) {
        self.queues
            .borrow_mut()
            .get_mut(&self.queue_num.get())
            .unwrap()
            .avail_ring = address;
    }

    fn set_used_ring(&self, address: u64) {
        self.queues
            .borrow_mut()
            .get_mut(&self.queue_num.get())
            .unwrap()
            .used_ring = address;
    }

    fn set_queue_enable(&self) {
        self.queues
            .borrow_mut()
            .get_mut(&self.queue_num.get())
            .unwrap()
            .enabled = true;
    }

    fn notify_queue(&self, queue: u16) {
        self.queues.borrow_mut().get_mut(&queue).unwrap().notified = true;
    }

    fn read_device_config(&self, offset: u64) -> u32 {
        *self.config.borrow_mut().get(&offset).unwrap()
    }
}
