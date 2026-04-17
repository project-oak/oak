//
// Copyright 2024 The Project Oak Authors
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

use alloc::{boxed::Box, vec::Vec};

use oak_restricted_kernel_interface::{EVENT_LOG_FD, Errno};

use super::fd::{FileDescriptor, copy_max_slice};

const MAX_EVENT_LOG_SIZE: usize = 4096; // 4 KiB

enum EventLogState {
    Reading,
    Writing,
}

pub struct EventLogDescriptor {
    state: EventLogState,
    data: Vec<u8>,
    index: usize,
}

impl EventLogDescriptor {
    pub fn new(mut data: Vec<u8>) -> Self {
        assert!(data.len() <= MAX_EVENT_LOG_SIZE, "initial event log data too large");
        // Allocate the max size upfront, so that syscalls does not result in
        // new allocations in kernel space later.
        {
            let additional = MAX_EVENT_LOG_SIZE - data.capacity();
            if additional > 0 {
                data.reserve(additional);
            }
        }
        Self { state: EventLogState::Reading, data, index: 0 }
    }
}

impl FileDescriptor for EventLogDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, Errno> {
        match self.state {
            EventLogState::Writing => {
                self.state = EventLogState::Reading;
                self.index = 0;
                self.read(buf)
            }
            EventLogState::Reading => {
                let length = copy_max_slice(&self.data[self.index..], buf);
                self.index += length;
                Ok(length as isize)
            }
        }
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno> {
        match self.state {
            EventLogState::Reading => {
                self.state = EventLogState::Writing;
                self.data.clear();
                self.index = 0;
                self.write(buf)
            }
            EventLogState::Writing => {
                let remaining_space = MAX_EVENT_LOG_SIZE.saturating_sub(self.data.len());
                let write_length = buf.len().min(remaining_space);
                self.data.extend_from_slice(&buf[..write_length]);
                if write_length < buf.len() {
                    Err(Errno::EINVAL)
                } else {
                    Ok(write_length as isize)
                }
            }
        }
    }

    fn sync(&mut self) -> Result<(), Errno> {
        Ok(())
    }
}

/// Registers a file descriptor for reading and writing event log data
pub fn register(encoded_event_log: Vec<u8>) {
    super::fd::register(EVENT_LOG_FD, Box::new(EventLogDescriptor::new(encoded_event_log)))
        .map_err(|_| ()) // throw away the box
        .expect("EventLogDescriptor already registered");
}

#[test]
fn test_read_write_cycle() {
    let initial_data = vec![1, 2, 3, 4, 5];
    let mut descriptor = EventLogDescriptor::new(initial_data);

    // Test initial read
    let mut read_buf = [0u8; 10];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 5);
    assert_eq!(&read_buf[..5], &[1, 2, 3, 4, 5]);

    // Test write after read
    let write_data = [6, 7, 8, 9, 10];
    assert_eq!(descriptor.write(&write_data).unwrap(), 5);

    // Test read after write
    let mut read_buf = [0u8; 10];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 5);
    assert_eq!(&read_buf[..5], &[6, 7, 8, 9, 10]);
}

#[test]
fn test_partial_read_write() {
    let initial_data = vec![1, 2, 3, 4, 5];
    let mut descriptor = EventLogDescriptor::new(initial_data);

    // Partial read
    let mut read_buf = [0u8; 3];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 3);
    assert_eq!(&read_buf, &[1, 2, 3]);

    // Remaining read
    let mut read_buf = [0u8; 3];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 2);
    assert_eq!(&read_buf[..2], &[4, 5]);

    // Write new data
    let write_data = [6, 7, 8];
    assert_eq!(descriptor.write(&write_data).unwrap(), 3);

    // Partial read of new data
    let mut read_buf = [0u8; 2];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 2);
    assert_eq!(&read_buf, &[6, 7]);

    // Remaining read of new data
    let mut read_buf = [0u8; 2];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 1);
    assert_eq!(&read_buf[..1], &[8]);
}

#[test]
fn test_multiple_writes() {
    let initial_data = vec![1, 2, 3];
    let mut descriptor = EventLogDescriptor::new(initial_data);

    // Read initial data
    let mut read_buf = [0u8; 3];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 3);
    assert_eq!(&read_buf, &[1, 2, 3]);

    // Multiple writes
    assert_eq!(descriptor.write(&[4, 5]).unwrap(), 2);
    assert_eq!(descriptor.write(&[6, 7, 8]).unwrap(), 3);

    // Read after multiple writes
    let mut read_buf = [0u8; 10];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 5);
    assert_eq!(&read_buf[..5], &[4, 5, 6, 7, 8]);
}

#[test]
fn test_error_cases() {
    let initial_data = vec![1, 2, 3];
    let mut descriptor = EventLogDescriptor::new(initial_data);

    // Attempt to write before reading everything should fail
    assert!(descriptor.write(&[4, 5]).is_err());

    // Read all data
    let mut read_buf = [0u8; 3];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 3);

    // Write some data
    assert_eq!(descriptor.write(&[4, 5]).unwrap(), 2);

    // Attempt to write again should succeed
    assert_eq!(descriptor.write(&[6, 7]).unwrap(), 2);

    // Read after write
    let mut read_buf = [0u8; 10];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 4);
    assert_eq!(&read_buf[..4], &[4, 5, 6, 7]);
}

#[test]
fn test_max_size_limit() {
    let mut descriptor = EventLogDescriptor::new(Vec::new());

    // Write 4 KiB of data
    let data = [0u8; MAX_EVENT_LOG_SIZE];
    assert_eq!(descriptor.write(&data).unwrap(), MAX_EVENT_LOG_SIZE as isize);

    // Attempt to write one more byte should fail
    assert_eq!(descriptor.write(&[1]).unwrap_err(), Errno::ENOSPC);

    // Read should return exactly 4 KiB
    let mut read_buf = [0u8; MAX_EVENT_LOG_SIZE + 1];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), MAX_EVENT_LOG_SIZE as isize);

    // Another read should return 0 bytes
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), 0);
}

#[test]
fn test_partial_write_at_limit() {
    let mut descriptor = EventLogDescriptor::new(Vec::new());

    // Write 4095 bytes
    let data = [0u8; MAX_EVENT_LOG_SIZE - 1];
    assert_eq!(descriptor.write(&data).unwrap(), (MAX_EVENT_LOG_SIZE - 1) as isize);

    // Write 2 more bytes, only 1 should be written
    assert_eq!(descriptor.write(&[1, 2]).unwrap(), 1);

    // Attempt to write more should fail
    assert_eq!(descriptor.write(&[3]).unwrap_err(), Errno::ENOSPC);

    // Read should return exactly 4 KiB
    let mut read_buf = [0u8; MAX_EVENT_LOG_SIZE + 1];
    assert_eq!(descriptor.read(&mut read_buf).unwrap(), MAX_EVENT_LOG_SIZE as isize);
    assert_eq!(read_buf[MAX_EVENT_LOG_SIZE - 1], 1);
}
