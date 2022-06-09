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

use super::*;
use crate::test::{
    new_legacy_transport, new_transport_small_queue, new_valid_transport, DeviceStatus,
    VIRTIO_F_VERSION_1,
};
use alloc::{vec, vec::Vec};
use ciborium_io::{Read, Write};

#[test]
fn test_legacy_device_not_supported() {
    let device = VirtioBaseDevice::new(new_legacy_transport());
    let mut console = Console::new(device);
    assert!(console.init().is_err());
}

#[test]
fn test_max_queue_size_too_small() {
    let device = VirtioBaseDevice::new(new_transport_small_queue());
    let mut console = Console::new(device);
    assert!(console.init().is_err());
}

#[test]
fn test_device_init() {
    let transport = new_valid_transport();
    let config = transport.config.clone();
    let device = VirtioBaseDevice::new(transport);
    let mut console = Console::new(device);
    let result = console.init();
    assert!(result.is_ok());

    let config = config.lock().unwrap();
    assert!(config.features == VIRTIO_F_VERSION_1);
    let status = DeviceStatus::from_bits(config.status).unwrap();
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_ACKNOWLEDGE));
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_DRIVER));
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_DRIVER_OK));
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_FEATURES_OK));
    assert!(!status.contains(DeviceStatus::VIRTIO_STATUS_FAILED));

    let queues = &config.queues;
    assert_eq!(queues.len(), 2);
    for i in 0..2 {
        let queue = queues.get(&i).unwrap();
        assert!(queue.enabled);
        assert_eq!(queue.queue_size as usize, QUEUE_SIZE);
        assert!(queue.descriptor_address > 0);
        assert!(queue.avail_ring > 0);
        assert!(queue.used_ring > 0);
    }
}

#[test]
fn test_read_bytes() {
    let data = vec![2, 4, 6];
    let transport = new_valid_transport();
    let device = VirtioBaseDevice::new(transport.clone());
    let mut console = Console::new(device);
    console.init().unwrap();
    transport.device_write_to_queue::<QUEUE_SIZE>(0, &data[..]);
    let bytes = console.read_bytes().unwrap();
    let bytes: Vec<u8> = bytes.into_iter().collect();
    assert_eq!(data, bytes);
}

#[test]
fn test_write_bytes() {
    let data = vec![7; 5];
    let transport = new_valid_transport();
    let device = VirtioBaseDevice::new(transport.clone());
    let mut console = Console::new(device);
    console.init().unwrap();
    let len = console.write_bytes(&data[..]).unwrap();
    assert_eq!(len, 5);
    let bytes = transport
        .device_read_once_from_queue::<QUEUE_SIZE>(1)
        .unwrap();
    assert_eq!(data, bytes);
}

#[test]
fn test_read_exact() {
    let data = vec![4; 10];
    let mut first = vec![0; 5];
    let mut second = vec![0; 3];
    let transport = new_valid_transport();
    let device = VirtioBaseDevice::new(transport.clone());
    let mut console = Console::new(device);
    console.init().unwrap();
    transport.device_write_to_queue::<QUEUE_SIZE>(0, &data[..]);
    assert!(console.read_exact(&mut first).is_ok());
    assert!(console.read_exact(&mut second).is_ok());
    assert_eq!(&data[..5], &first[..]);
    assert_eq!(&data[5..8], &second[..]);
    assert!(console.pending_data.is_some());
    assert_eq!(console.pending_data.unwrap().len(), 2);
}

#[test]
fn test_write_all() {
    let data = vec![13; 5000];
    let transport = new_valid_transport();
    let device = VirtioBaseDevice::new(transport.clone());
    let mut console = Console::new(device);
    console.init().unwrap();
    assert!(console.write_all(&data[..]).is_ok());
    let first = transport
        .device_read_once_from_queue::<QUEUE_SIZE>(1)
        .unwrap();
    let second = transport
        .device_read_once_from_queue::<QUEUE_SIZE>(1)
        .unwrap();
    assert_eq!(&data[..DATA_BUFFER_SIZE], &first[..]);
    assert_eq!(&data[DATA_BUFFER_SIZE..], &second[..]);
}
