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

use alloc::alloc::Global;

use super::*;
use crate::test::{
    identity_map, inverse_identity_map, new_legacy_transport, new_transport_small_queue,
    new_valid_transport, DeviceStatus, TestingTransport, VIRTIO_F_VERSION_1,
};

const GUEST_CID: u64 = 3;

#[test]
fn test_legacy_device_not_supported() {
    let device = VirtioBaseDevice::new(new_legacy_transport());
    let mut vsock = VSock::new(device, identity_map, &Global);
    assert!(vsock.init(identity_map, inverse_identity_map).is_err());
}

#[test]
fn test_max_queue_size_too_small() {
    let device = VirtioBaseDevice::new(new_transport_small_queue());
    let mut vsock = VSock::new(device, identity_map, &Global);
    assert!(vsock.init(identity_map, inverse_identity_map).is_err());
}

#[test]
fn test_device_init() {
    let transport = new_configured_transport();
    let config = transport.config.clone();
    let device = VirtioBaseDevice::new(transport);
    let mut vsock = VSock::new(device, identity_map, &Global);
    let result = vsock.init(identity_map, inverse_identity_map);
    assert!(result.is_ok());

    let config = config.lock().unwrap();
    assert!(config.features == VIRTIO_F_VERSION_1);
    let status = DeviceStatus::from_bits(config.status).unwrap();
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_ACKNOWLEDGE));
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_DRIVER));
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_DRIVER_OK));
    assert!(status.contains(DeviceStatus::VIRTIO_STATUS_FEATURES_OK));
    assert!(!status.contains(DeviceStatus::VIRTIO_STATUS_FAILED));
    assert_eq!(vsock.guest_cid, GUEST_CID);

    let queues = &config.queues;
    assert_eq!(queues.len(), 3);
    for i in 0..3 {
        let queue = queues.get(&i).unwrap();
        assert!(queue.enabled);
        assert_eq!(queue.queue_size as usize, QUEUE_SIZE);
        assert!(!queue.descriptor_address.is_null());
        assert!(!queue.avail_ring.is_null());
        assert!(!queue.used_ring.is_null());
    }
}

#[test]
fn test_read_packet() {
    let data = [2, 4, 6];
    let mut packet = Packet::new_data(&data[..], 1, 2).unwrap();
    packet.set_dst_cid(GUEST_CID);
    packet.set_src_cid(HOST_CID);
    let transport = new_configured_transport();
    let device = VirtioBaseDevice::new(transport.clone());
    let mut vsock = VSock::new(device, identity_map, &Global);
    vsock.init(identity_map, inverse_identity_map).unwrap();
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    let result = vsock.read_packet().unwrap();
    assert_eq!(packet.as_slice(), result.as_slice());
}

#[test]
fn test_write_packet() {
    let data = [7; 5];
    let mut packet = Packet::new_data(&data[..], 1, 2).unwrap();
    let transport = new_configured_transport();
    let device = VirtioBaseDevice::new(transport.clone());
    let mut vsock = VSock::new(device, identity_map, &Global);
    vsock.init(identity_map, inverse_identity_map).unwrap();
    vsock.write_packet(&mut packet);
    let bytes = transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap();
    assert_eq!(packet.as_slice(), &bytes[..]);
}

fn new_configured_transport() -> TestingTransport {
    let transport = new_valid_transport();
    transport.write_device_config(0, GUEST_CID as u32);
    transport
}
