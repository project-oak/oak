//
// Copyright 2020 The Project Oak Authors
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

//! Provides implementations of Oak ABI functions to test the async executor against.
//!
//! `init()` must be called at the start of each test case, or state from a previous test run on the
//! same thread may interfere with later tests.
//!
//! The following functions are available to modify the result of Runtime ABI calls:
//! * `set_wait_on_channels_handler`: Configures a handler function that can set statuses for
//!   channels when `wait_on_channels` is called.
//! * `add_ready_data`: Adds a `Message` to the queue for a handle. Calls to `channel_read` will
//!   return the values in this queue in insertion order.
//! * `set_error`: Adds an error status into the queue for a handle.

use core::cell::RefCell;
use oak::io::Encodable;
use oak_abi::{
    proto::oak::{ChannelReadStatus, OakStatus},
    Handle,
};
use std::collections::{HashMap, VecDeque};

pub fn init() {
    WAIT_ON_CHANNELS_HANDLER.with(|handler| handler.replace(None));
    READY_DATA.with(|ready_data| ready_data.borrow_mut().clear());
}

#[repr(packed)]
pub struct HandleWithStatus {
    handle: Handle,
    status: u8,
}

impl HandleWithStatus {
    pub fn handle(&self) -> Handle {
        self.handle
    }

    pub fn set_status(&mut self, status: ChannelReadStatus) {
        self.status = status as i32 as u8;
    }
}

#[no_mangle]
pub extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> u32 {
    let handles =
        unsafe { core::slice::from_raw_parts_mut(buf as *mut HandleWithStatus, count as usize) };
    WAIT_ON_CHANNELS_HANDLER.with(|handler| {
        (handler
            .borrow_mut()
            .as_mut()
            .expect("no wait_on_channels handler configured"))(handles)
    }) as i32 as u32
}

/// Stub function necessary for Oak ABI.
#[no_mangle]
pub extern "C" fn wait_on_channels_with_downgrade(_buf: *mut u8, _count: u32) -> u32 {
    0
}

type WaitOnChannelsHandler = Box<dyn FnMut(&mut [HandleWithStatus]) -> OakStatus>;
std::thread_local! {
    static WAIT_ON_CHANNELS_HANDLER: RefCell<Option<WaitOnChannelsHandler>> = RefCell::new(None);
}

pub fn set_wait_on_channels_handler<F: 'static + FnMut(&mut [HandleWithStatus]) -> OakStatus>(
    handler: F,
) {
    WAIT_ON_CHANNELS_HANDLER.with(|cell| cell.replace(Some(Box::new(handler))));
}

#[no_mangle]
pub extern "C" fn channel_read(
    handle: Handle,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: u32,
    actual_handle_count: *mut u32,
) -> u32 {
    READY_DATA.with(|ready_data| {
        let mut ready_data = ready_data.borrow_mut();
        let data_queue = ready_data.entry(handle).or_default();
        let status = match data_queue.front() {
            None => OakStatus::ErrChannelEmpty,
            Some(Err(status)) => *status,
            Some(Ok(data)) if data.len() > size => {
                unsafe { *actual_size = data.len() as u32 };
                OakStatus::ErrBufferTooSmall
            }
            Some(Ok(data)) => {
                unsafe {
                    let buf = core::slice::from_raw_parts_mut(buf, data.len());
                    buf.copy_from_slice(data);
                    *actual_size = data.len() as u32;
                    *actual_handle_count = 0;
                };
                let _ = data_queue.pop_front();
                OakStatus::Ok
            }
        };
        status as i32 as u32
    })
}

/// Stub function necessary for Oak ABI.
#[no_mangle]
pub extern "C" fn channel_read_with_downgrade(
    _handle: Handle,
    _buf: *mut u8,
    _size: usize,
    _actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: u32,
    _actual_handle_count: *mut u32,
) -> u32 {
    0
}

type ReadyChannelData = VecDeque<Result<Vec<u8>, OakStatus>>;

std::thread_local! {
    static READY_DATA: RefCell<HashMap<Handle, ReadyChannelData>> = RefCell::new(HashMap::new());
}

pub fn add_ready_data<T: Encodable>(handle: Handle, data: &T) {
    let msg = data.encode().expect("Failed to encode ready data");
    READY_DATA.with(|ready_data| {
        ready_data
            .borrow_mut()
            .entry(handle)
            .or_default()
            .push_back(Ok(msg.bytes))
    });
}

// Note: this status is added into the queue of ready data, so any previously add ready data must
// first be read before this status will be returned. The channel status is never removed, any
// future reads will always return this error status.
pub fn set_error(handle: Handle, status: OakStatus) {
    assert_ne!(status, OakStatus::Ok);
    READY_DATA.with(|ready_data| {
        ready_data
            .borrow_mut()
            .entry(handle)
            .or_default()
            .push_back(Err(status))
    });
}
