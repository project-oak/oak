//
// Copyright 2019 The Project Oak Authors
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

//! Test utilities to help with unit testing of Oak SDK code.

extern crate protobuf;

use oak::OakStatus;
use protobuf::ProtobufEnum;
use std::cell::RefCell;
use std::collections::VecDeque;

pub mod proto;
#[cfg(test)]
mod tests;

struct MockChannel {
    /// If read_status is set, this status value will be returned for any read
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    pub read_status: Option<u32>,
    /// If write_status is set, this status value will be returned for any write
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    pub write_status: Option<u32>,
    /// Pending messages on the channel
    pub messages: VecDeque<Vec<u8>>,
}

impl MockChannel {
    fn new() -> MockChannel {
        MockChannel {
            read_status: None,
            write_status: None,
            messages: VecDeque::new(),
        }
    }
    fn write_message(&mut self, buf: *const u8, size: usize) -> u32 {
        if let Some(status) = self.write_status {
            return status;
        }
        let mut msg = Vec::with_capacity(size);
        unsafe {
            std::ptr::copy_nonoverlapping(buf, msg.as_mut_ptr(), size);
            msg.set_len(size);
        }
        self.messages.push_back(msg);
        OakStatus::OK.value() as u32
    }
    fn read_message(&mut self, buf: *mut u8, size: usize, actual_size: *mut u32) -> u32 {
        if let Some(status) = self.read_status {
            return status;
        }
        let msg = self.messages.pop_front();
        if msg.is_none() {
            unsafe { *actual_size = 0 }
            return OakStatus::OK.value() as u32;
        }
        let msg = msg.unwrap();

        let len = msg.len();
        unsafe { *actual_size = len as u32 }
        if len > size {
            self.messages.push_front(msg);
            return OakStatus::ERR_BUFFER_TOO_SMALL.value() as u32;
        }
        unsafe {
            std::ptr::copy_nonoverlapping(msg.as_ptr(), buf, len);
        }
        OakStatus::OK.value() as u32
    }
}

// Test-only mock channel which is used to service any calls to channel_read
// or channel_write, regardless of channel handle.
thread_local! {
    static CHANNEL: RefCell<MockChannel> = RefCell::new(MockChannel::new());
}

// Implementations of the Oak API host functions in Rust for testing.

/// Test-only implementation of channel wait functionality, which always
/// indicates that all provided channels are ready for reading.
#[no_mangle]
pub unsafe extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> u32 {
    // Pretend all channels are readable.
    for i in 0..(count as usize) {
        let p = buf
            .add(i * oak::wasm::SPACE_BYTES_PER_HANDLE + (oak::wasm::SPACE_BYTES_PER_HANDLE - 1));
        *p = 1;
    }
    OakStatus::OK.value() as u32
}

/// Test-only implementation of channel write functionality, which writes (only) the data
/// of the provided message to a (global) test channel.
#[no_mangle]
pub extern "C" fn channel_write(
    _handle: u64,
    buf: *const u8,
    size: usize,
    _handle_buf: *const u8,
    _handle_count: u32,
) -> u32 {
    CHANNEL.with(|channel| channel.borrow_mut().write_message(buf, size))
}

/// Test-only implementation fo channel read functionality, which reads a
/// message from the (global) test channel.
#[no_mangle]
pub extern "C" fn channel_read(
    _handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: u32,
    _actual_handle_count: *mut u32,
) -> u32 {
    CHANNEL.with(|channel| channel.borrow_mut().read_message(buf, size, actual_size))
}

/// Test-only placeholder for channel creation, which always fails.
#[no_mangle]
pub extern "C" fn channel_create(_write: *mut u64, _read: *mut u64) -> u32 {
    OakStatus::ERR_INTERNAL.value() as u32
}

/// Test-only placeholder for channel creation, which always appears to succeed
/// (but does nothing).
#[no_mangle]
pub extern "C" fn channel_close(_handle: u64) -> u32 {
    OakStatus::OK.value() as u32
}

/// Test-only placeholder for finding a channel by preconfigured port name, which
/// always returns a hard coded value.
#[no_mangle]
pub extern "C" fn channel_find(_buf: *const u8, _size: usize) -> u64 {
    1
}

/// Test-only placeholder for random data generation.
#[no_mangle]
pub unsafe extern "C" fn random_get(buf: *mut u8, size: usize) -> u32 {
    for i in 0..size as isize {
        *(buf.offset(i)) = 4; // chosen by fair dice roll
    }
    OakStatus::OK.value() as u32
}

/// Convenience test helper which returns the last message on the global test
/// channel as a string.
pub fn last_message_as_string() -> String {
    CHANNEL.with(|channel| match channel.borrow().messages.front() {
        Some(msg) => unsafe { std::str::from_utf8_unchecked(msg).to_string() },
        None => "".to_string(),
    })
}

/// Test helper that injects a failure for future channel read operations.
pub fn set_read_status(status: Option<u32>) {
    CHANNEL.with(|channel| channel.borrow_mut().read_status = status)
}

/// Test helper that injects a failure for future channel write operations.
pub fn set_write_status(status: Option<u32>) {
    CHANNEL.with(|channel| channel.borrow_mut().write_status = status)
}

/// Test helper that sets up a new global test channel.
pub fn reset_channels() {
    CHANNEL.with(|channel| *channel.borrow_mut() = MockChannel::new())
}
