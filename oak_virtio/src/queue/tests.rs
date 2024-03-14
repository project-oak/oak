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

use alloc::{alloc::Global, vec};

use super::*;
use crate::test::identity_map;

const QUEUE_SIZE: usize = 4;
const BUFFER_SIZE: usize = 4;

#[test]
fn test_read_empty_queue() {
    let mut queue =
        DeviceWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);
    let data = queue.read_next_used_buffer();
    assert!(data.is_none());
    assert_eq!(queue.inner.last_used_idx.0, 0);
    assert_eq!(queue.inner.virt_queue.used.idx.0, 0);
    assert_eq!(queue.inner.virt_queue.avail.idx.0 as usize, QUEUE_SIZE);
}

#[test]
#[should_panic]
fn test_invalid_queue_size() {
    // `QUEUE_SIZE` must be a power of 2.
    let _ = Queue::<3, BUFFER_SIZE, Global>::new(DescFlags::empty(), identity_map, &Global);
}

#[test]
fn test_read_once() {
    let data = vec![0, 1, 2];
    let mut queue =
        DeviceWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);

    let result = device_write(queue.inner.virt_queue.as_mut(), &data);
    assert_eq!(Some(3), result);
    assert_eq!(queue.inner.last_used_idx.0, 0);
    assert_eq!(queue.inner.virt_queue.used.idx.0, 1);
    assert_eq!(queue.inner.virt_queue.used.ring[0].len, 3);
    assert_eq!(queue.inner.virt_queue.avail.idx.0 as usize, QUEUE_SIZE);

    let read = queue.read_next_used_buffer();
    assert_eq!(queue.inner.last_used_idx.0, 1);
    assert_eq!(Some(data), read);
    assert_eq!(queue.inner.virt_queue.avail.idx.0 as usize, QUEUE_SIZE + 1);
}

#[test]
fn test_write_once() {
    let data = vec![0, 1, 2];
    let mut queue =
        DriverWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);

    let result = queue.write_buffer(&data);
    assert_eq!(Some(3), result);
    assert_eq!(queue.inner.virt_queue.avail.idx.0 as usize, 1);

    let read = device_read_once(queue.inner.virt_queue.as_mut());
    assert_eq!(queue.inner.virt_queue.used.idx.0, 1);
    assert_eq!(Some(data), read);
}

#[test]
fn test_wrapping_idx() {
    let data = vec![0, 1, 2];
    let mut queue =
        DriverWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);

    // Move the indices along to the max value.
    queue.inner.virt_queue.avail.idx = Wrapping(u16::MAX);
    queue.inner.virt_queue.used.idx = Wrapping(u16::MAX);
    queue.inner.last_used_idx = Wrapping(u16::MAX);

    let result = queue.write_buffer(&data);
    assert_eq!(Some(3), result);
    assert_eq!(queue.inner.virt_queue.avail.idx.0 as usize, 0);

    let read = device_read_once(queue.inner.virt_queue.as_mut());
    assert_eq!(queue.inner.virt_queue.used.idx.0, 0);
    assert_eq!(Some(data), read);
}

#[test]
fn test_write_too_long() {
    let data = vec![0, 1, 2, 3, 4];
    let mut queue =
        DriverWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);

    let result = queue.write_buffer(&data);
    assert_eq!(Some(4), result);
}

#[test]
fn test_device_queue_exhaustion() {
    let mut queue =
        DeviceWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);
    let data = Some(vec![0]);
    // We can write 4 times.
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(Some(1), result);
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(Some(1), result);
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(Some(1), result);
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(Some(1), result);
    // The 5th time should not write.
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(None, result);
    // Read twice to make space.
    let result = queue.read_next_used_buffer();
    assert_eq!(data, result);
    let result = queue.read_next_used_buffer();
    assert_eq!(data, result);
    // Now we can write twice.
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(Some(1), result);
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(Some(1), result);
    // But the 3rd time should be blocked again.
    let result = device_write(queue.inner.virt_queue.as_mut(), data.as_ref().unwrap());
    assert_eq!(None, result);
}

#[test]
fn test_driver_queue_exhaustion() {
    let mut queue =
        DriverWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);
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
    let result = device_read_once(queue.inner.virt_queue.as_mut());
    assert_eq!(data, result);
    let result = device_read_once(queue.inner.virt_queue.as_mut());
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
    let mut tx =
        DriverWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);
    let mut rx =
        DeviceWriteOnlyQueue::<QUEUE_SIZE, BUFFER_SIZE, Global>::new(identity_map, &Global);
    for _ in 0..100 {
        // Run batches of 3 echos or different data lengths repeatedly.
        tx.write_buffer(data_1.as_ref().unwrap()).unwrap();
        tx.write_buffer(data_2.as_ref().unwrap()).unwrap();
        tx.write_buffer(data_3.as_ref().unwrap()).unwrap();

        for _ in 0..3 {
            let tmp = device_read_once(tx.inner.virt_queue.as_mut()).unwrap();
            device_write(rx.inner.virt_queue.as_mut(), &tmp).unwrap();
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

    let ring_index = virt_queue.used.idx.0 as usize % QUEUE_SIZE;
    let index = virt_queue.avail.ring[ring_index];
    let desc = &virt_queue.desc[index as usize];
    assert!(!desc.flags.contains(DescFlags::VIRTQ_DESC_F_WRITE));
    let used_elem = &mut virt_queue.used.ring[ring_index];
    used_elem.id = index as u32;
    used_elem.len = 0;
    virt_queue.used.idx += 1;
    // Safety: we purposely use unsafe code to simulate the way the the device/VMM
    // will interact with the memory. We treat the contents of the slice as data
    // only and ensure we only pass valid addresses and sizes from the tests.
    let buffer = unsafe {
        let ptr = desc.addr.as_u64() as usize as *const u8;
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
    let ring_index = virt_queue.used.idx.0 as usize % QUEUE_SIZE;
    let index = virt_queue.avail.ring[ring_index];
    let desc = &virt_queue.desc[index as usize];
    assert!(desc.flags.contains(DescFlags::VIRTQ_DESC_F_WRITE));
    let used_elem = &mut virt_queue.used.ring[ring_index];
    used_elem.id = index as u32;
    used_elem.len = len as u32;
    virt_queue.used.idx += 1;
    // Safety: we purposely use unsafe code to simulate the way the the device/VMM
    // will interact with the memory. We treat the contents of the slice as data
    // only and ensure we only pass valid addresses and lengths from the tests.
    let buffer = unsafe {
        let ptr = desc.addr.as_u64() as usize as *mut u8;
        alloc::slice::from_raw_parts_mut(ptr, len)
    };
    buffer.copy_from_slice(data);
    Some(len)
}
