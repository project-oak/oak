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

use alloc::{collections::BTreeMap, sync::Arc, vec::Vec};
use core::mem::size_of;
use std::sync::Mutex;

use bitflags::bitflags;
use rust_hypervisor_firmware_virtio::virtio::{Error, VirtioTransport};
use x86_64::{PhysAddr, VirtAddr};

use crate::queue::virtq::{AvailRing, Desc, DescFlags, UsedRing};

/// Virtio Version 1 feature bit.
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-4100006>.
pub const VIRTIO_F_VERSION_1: u64 = 1 << 32;

bitflags! {
    /// Virtio device status flags.
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-100001>.
    pub struct DeviceStatus: u32 {
        const VIRTIO_STATUS_ACKNOWLEDGE = 1;
        const VIRTIO_STATUS_DRIVER = 2;
        const VIRTIO_STATUS_FEATURES_OK = 8;
        const VIRTIO_STATUS_DRIVER_OK = 4;
        const VIRTIO_STATUS_FAILED = 128;
    }
}

/// A transport implementation that can be used for testing virtio device implementations.
#[derive(Default, Debug, Clone)]
pub struct TestingTransport {
    pub config: Arc<Mutex<TestingConfig>>,
}

/// Configuration information required by `TestingTransport`.
#[derive(Default, Debug)]
pub struct TestingConfig {
    pub status: u32,
    pub features: u64,
    pub queue_num: u16,
    pub max_queue_size: u16,
    pub queues: BTreeMap<u16, QueueInfo>,
    pub config: BTreeMap<u64, u32>,
}

/// Information about a virtqueue.
#[derive(Debug)]
pub struct QueueInfo {
    pub queue_size: u16,
    pub descriptor_address: PhysAddr,
    pub avail_ring: PhysAddr,
    pub used_ring: PhysAddr,
    pub enabled: bool,
    pub notified: bool,
}

impl Default for QueueInfo {
    fn default() -> Self {
        Self {
            queue_size: Default::default(),
            descriptor_address: PhysAddr::zero(),
            avail_ring: PhysAddr::zero(),
            used_ring: PhysAddr::zero(),
            enabled: Default::default(),
            notified: Default::default(),
        }
    }
}

impl TestingTransport {
    /// Tries to read once from the specified queue as if it was a device.
    ///
    /// Warning: we purposely use unsafe code to simulate the way the the device/VMM will interact
    /// with the memory. Tests must ensure that valid memory and offset values are provided to
    /// avoid memory safety issues.
    pub fn device_read_once_from_queue<const QUEUE_SIZE: usize>(
        &self,
        queue_num: u16,
    ) -> Option<Vec<u8>> {
        let avail = self.get_avail_ring::<QUEUE_SIZE>(queue_num);
        let used = self.get_used_ring::<QUEUE_SIZE>(queue_num);
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
            let ptr = desc.addr.as_u64() as usize as *const u8;
            let len = desc.length as usize;
            alloc::slice::from_raw_parts(ptr, len)
        };
        Some(buffer.to_vec())
    }

    /// Tries to write to the specified queue as if it was a device.
    ///
    /// Warning: we purposely use unsafe code to simulate the way the the device/VMM will interact
    /// with the memory. Tests must ensure that valid memory and offset values are provided to
    /// avoid memory safety issues.
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
        used_elem.len = len as u32;
        used.idx += 1;
        let buffer = unsafe {
            let ptr = desc.addr.as_u64() as usize as *mut u8;
            alloc::slice::from_raw_parts_mut(ptr, len)
        };
        buffer.copy_from_slice(data);
        Some(len)
    }

    /// Writes a value to the device configuration at the specified offset.
    pub fn write_device_config(&self, offset: u64, value: u32) {
        self.config.lock().unwrap().config.insert(offset, value);
    }

    #[allow(clippy::mut_from_ref)]
    fn get_desc<const QUEUE_SIZE: usize>(&self, queue_num: u16, index: u16) -> &mut Desc {
        assert!((index as usize) < QUEUE_SIZE);
        let config = self.config.lock().unwrap();
        let queue_info = config.queues.get(&queue_num).unwrap();
        let address =
            queue_info.descriptor_address.as_u64() as usize + index as usize * size_of::<Desc>();
        unsafe { &mut *(address as *mut Desc) }
    }

    #[allow(clippy::mut_from_ref)]
    fn get_avail_ring<const QUEUE_SIZE: usize>(&self, queue_num: u16) -> &AvailRing<QUEUE_SIZE> {
        let config = self.config.lock().unwrap();
        let queue_info = config.queues.get(&queue_num).unwrap();
        let address = queue_info.avail_ring.as_u64() as usize;
        unsafe { &*(address as *mut AvailRing<QUEUE_SIZE>) }
    }

    #[allow(clippy::mut_from_ref)]
    fn get_used_ring<const QUEUE_SIZE: usize>(&self, queue_num: u16) -> &mut UsedRing<QUEUE_SIZE> {
        let config = self.config.lock().unwrap();
        let queue_info = config.queues.get(&queue_num).unwrap();
        let address = queue_info.used_ring.as_u64() as usize;
        unsafe { &mut *(address as *mut UsedRing<QUEUE_SIZE>) }
    }
}

impl VirtioTransport for TestingTransport {
    fn init<X: Fn(PhysAddr) -> Option<VirtAddr>>(
        &mut self,
        _device_type: u32,
        _translator: X,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_status(&self) -> u32 {
        self.config.lock().unwrap().status
    }

    fn set_status(&self, status: u32) {
        self.config.lock().unwrap().status = status;
    }

    fn add_status(&self, status: u32) {
        self.set_status(self.get_status() | status);
    }

    fn reset(&self) {
        self.config.lock().unwrap().status = 0;
    }

    fn get_features(&self) -> u64 {
        self.config.lock().unwrap().features
    }

    fn set_features(&self, features: u64) {
        self.config.lock().unwrap().features = features;
    }

    fn set_queue(&self, queue: u16) {
        let mut config = self.config.lock().unwrap();
        config.queues.entry(queue).or_default();
        config.queue_num = queue;
    }

    fn get_queue_max_size(&self) -> u16 {
        self.config.lock().unwrap().max_queue_size
    }

    fn set_queue_size(&self, queue_size: u16) {
        let mut config = self.config.lock().unwrap();
        let queue_num = config.queue_num;
        assert!(queue_size <= config.max_queue_size);
        config.queues.get_mut(&queue_num).unwrap().queue_size = queue_size;
    }

    fn set_descriptors_address(&self, address: PhysAddr) {
        let mut config = self.config.lock().unwrap();
        let queue_num = config.queue_num;
        config
            .queues
            .get_mut(&queue_num)
            .unwrap()
            .descriptor_address = address;
    }

    fn set_avail_ring(&self, address: PhysAddr) {
        let mut config = self.config.lock().unwrap();
        let queue_num = config.queue_num;
        config.queues.get_mut(&queue_num).unwrap().avail_ring = address;
    }

    fn set_used_ring(&self, address: PhysAddr) {
        let mut config = self.config.lock().unwrap();
        let queue_num = config.queue_num;
        config.queues.get_mut(&queue_num).unwrap().used_ring = address;
    }

    fn set_queue_enable(&self) {
        let mut config = self.config.lock().unwrap();
        let queue_num = config.queue_num;
        config.queues.get_mut(&queue_num).unwrap().enabled = true;
    }

    fn notify_queue(&self, queue: u16) {
        self.config
            .lock()
            .unwrap()
            .queues
            .get_mut(&queue)
            .unwrap()
            .notified = true;
    }

    fn read_device_config(&self, offset: u64) -> u32 {
        *self.config.lock().unwrap().config.get(&offset).unwrap()
    }
}

/// Creates a new valid transport that is suitable for a basic device without configuration values.
pub fn new_valid_transport() -> TestingTransport {
    let transport = TestingTransport::default();
    {
        let mut config = transport.config.lock().unwrap();
        config.features = VIRTIO_F_VERSION_1;
        config.max_queue_size = 256;
    }
    transport
}

/// Creates a transport that only supports a legacy version of the virtio spec.
pub fn new_legacy_transport() -> TestingTransport {
    let transport = new_valid_transport();
    transport.set_features(0);
    transport
}

/// Creates a transport where the queue is too small.
pub fn new_transport_small_queue() -> TestingTransport {
    let transport = new_valid_transport();
    transport.config.lock().unwrap().max_queue_size = 8;
    transport
}

pub fn identity_map(addr: VirtAddr) -> Option<PhysAddr> {
    Some(PhysAddr::new(addr.as_u64()))
}

pub fn inverse_identity_map(addr: PhysAddr) -> Option<VirtAddr> {
    Some(VirtAddr::new(addr.as_u64()))
}
