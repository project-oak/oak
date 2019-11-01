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

#[macro_use]
extern crate log;
extern crate protobuf;
extern crate rand;

use oak::OakStatus;
use protobuf::ProtobufEnum;
use rand::Rng;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::sync::Once;

pub mod proto;
#[cfg(test)]
mod tests;

struct OakMessage {
    data: Vec<u8>,
}

struct MockChannel {
    /// If read_status is set, this status value will be returned for any read
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    read_status: Option<u32>,
    /// If write_status is set, this status value will be returned for any write
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    write_status: Option<u32>,
    /// Pending messages on the channel
    messages: VecDeque<OakMessage>,
}

impl MockChannel {
    fn new() -> MockChannel {
        MockChannel {
            read_status: None,
            write_status: None,
            messages: VecDeque::new(),
        }
    }
    fn write_message(&mut self, msg: OakMessage) -> u32 {
        if let Some(status) = self.write_status {
            return status;
        }
        self.messages.push_back(msg);
        OakStatus::OK.value() as u32
    }
    fn read_message(&mut self, size: usize, actual_size: &mut u32) -> Result<OakMessage, u32> {
        if let Some(status) = self.read_status {
            return Err(status);
        }
        let msg = self.messages.pop_front();
        if msg.is_none() {
            *actual_size = 0;
            return Err(OakStatus::OK.value() as u32);
        }
        let msg = msg.unwrap();
        let len = msg.data.len();
        *actual_size = len as u32;
        if len > size {
            self.messages.push_front(msg);
            return Err(OakStatus::ERR_BUFFER_TOO_SMALL.value() as u32);
        }
        Ok(msg)
    }
}

#[derive(PartialEq, Copy, Clone)]
enum Direction {
    Read,
    Write,
}

#[derive(PartialEq, Copy, Clone)]
struct ChannelHalf {
    direction: Direction,
    channel_idx: usize, // index into OakRuntime.channels
}

struct OakRuntime {
    termination_pending: bool,
    channels: Vec<MockChannel>,
    nodes: HashMap<String, OakNode>,
}

struct OakNode {
    next_handle: oak::Handle,
    halves: HashMap<oak::Handle, ChannelHalf>,
    ports: HashMap<String, oak::Handle>,
}

impl OakRuntime {
    fn new() -> OakRuntime {
        let mut nodes = HashMap::new();
        // TODO: cope with multi-Node applications
        nodes.insert(
            "app".to_string(),
            OakNode {
                next_handle: 1 as oak::Handle,
                halves: HashMap::new(),
                ports: HashMap::new(),
            },
        );
        OakRuntime {
            termination_pending: false,
            channels: Vec::new(),
            nodes,
        }
    }
    fn reset(&mut self) {
        let names: Vec<String> = self.nodes.keys().cloned().collect();
        for name in &names {
            let node = self.nodes.get_mut(name).unwrap();
            node.halves.clear();
            node.ports.clear();
        }
    }
    fn new_channel(&mut self) -> usize {
        let channel_idx = self.channels.len();
        self.channels.push(MockChannel::new());
        channel_idx
    }
    fn node_channel_create(&mut self, node_name: &str) -> (oak::Handle, oak::Handle) {
        let channel_idx = self.new_channel();
        let node = self.nodes.get_mut(node_name).unwrap();
        let write_handle = node.add_half(ChannelHalf {
            direction: Direction::Write,
            channel_idx,
        });
        let read_handle = node.add_half(ChannelHalf {
            direction: Direction::Read,
            channel_idx,
        });
        (write_handle, read_handle)
    }
    fn node_channel_write(&mut self, node_name: &str, handle: oak::Handle, msg: OakMessage) -> u32 {
        let node = self.nodes.get(node_name).unwrap();
        if !node.halves.contains_key(&handle) {
            return oak::OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        let half = node.halves.get(&handle).unwrap();
        if half.direction == Direction::Read {
            return oak::OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        self.channels[half.channel_idx].write_message(msg)
    }
    fn node_channel_read(
        &mut self,
        node_name: &str,
        handle: oak::Handle,
        size: usize,
        actual_size: &mut u32,
    ) -> Result<OakMessage, u32> {
        let node = self.nodes.get(node_name).unwrap();
        if !node.halves.contains_key(&handle) {
            return Err(oak::OakStatus::ERR_BAD_HANDLE.value() as u32);
        }
        let half = node.halves.get(&handle).unwrap();
        if half.direction == Direction::Write {
            return Err(oak::OakStatus::ERR_BAD_HANDLE.value() as u32);
        }
        self.channels[half.channel_idx].read_message(size, actual_size)
    }
}

impl OakNode {
    fn add_half(&mut self, half: ChannelHalf) -> oak::Handle {
        let handle = self.next_handle;
        self.next_handle += 1;
        self.halves.insert(handle, half);
        handle
    }
    fn close_channel(&mut self, handle: oak::Handle) -> u32 {
        if !self.halves.contains_key(&handle) {
            return OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        self.halves.remove(&handle);
        OakStatus::OK.value() as u32
    }
}

// Test-only mock runtime which is used to service any calls to TCB functionality.
thread_local! {
    static RUNTIME: RefCell<OakRuntime> = RefCell::new(OakRuntime::new());
}

// Implementations of the Oak API host functions in Rust for testing.
// These implementations generally handle the unsafe raw memory manipulation
// then forward on to the equivalent method on the current OakRuntime instance.

/// Test-only implementation of channel wait functionality, which always
/// indicates that all provided channels are ready for reading.
#[no_mangle]
pub unsafe extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> u32 {
    let termination_pending = RUNTIME.with(|runtime| runtime.borrow().termination_pending);
    if termination_pending {
        return OakStatus::ERR_TERMINATED.value() as u32;
    }
    for i in 0..(count as usize) {
        let p = buf
            .add(i * oak::wasm::SPACE_BYTES_PER_HANDLE + (oak::wasm::SPACE_BYTES_PER_HANDLE - 1));
        *p = oak::ChannelReadStatus::READ_READY
            .value()
            .try_into()
            .unwrap();
    }
    OakStatus::OK.value() as u32
}

/// Test-only implementation of channel write functionality, which writes (only) the data
/// of the provided message to a test channel.
#[no_mangle]
pub unsafe extern "C" fn channel_write(
    handle: u64,
    buf: *const u8,
    size: usize,
    _handle_buf: *const u8,
    _handle_count: u32,
) -> u32 {
    let mut msg = OakMessage {
        data: Vec::with_capacity(size),
    };
    std::ptr::copy_nonoverlapping(buf, msg.data.as_mut_ptr(), size);
    msg.data.set_len(size);

    RUNTIME.with(|runtime| runtime.borrow_mut().node_channel_write("app", handle, msg))
}

/// Test-only implementation of channel read functionality, which reads a
/// message from the test channel.
#[no_mangle]
pub unsafe extern "C" fn channel_read(
    handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: u32,
    _actual_handle_count: *mut u32,
) -> u32 {
    let mut asize = 0u32;
    let result = RUNTIME.with(|runtime| {
        runtime
            .borrow_mut()
            .node_channel_read("app", handle, size, &mut asize)
    });
    *actual_size = asize;
    match result {
        Ok(msg) => {
            std::ptr::copy_nonoverlapping(msg.data.as_ptr(), buf, asize as usize);
            oak::OakStatus::OK as u32
        }
        Err(status) => status,
    }
}

/// Test-only version of channel creation.
#[no_mangle]
pub unsafe extern "C" fn channel_create(write: *mut u64, read: *mut u64) -> u32 {
    let (write_handle, read_handle) =
        RUNTIME.with(|runtime| runtime.borrow_mut().node_channel_create("app"));

    *write = write_handle;
    *read = read_handle;
    OakStatus::OK.value() as u32
}

/// Test-only version of channel closure.
#[no_mangle]
pub extern "C" fn channel_close(handle: u64) -> u32 {
    RUNTIME.with(|runtime| {
        runtime
            .borrow_mut()
            .nodes
            .get_mut("app")
            .unwrap()
            .close_channel(handle)
    })
}

/// Test-only placeholder for finding a channel by preconfigured port name.
#[no_mangle]
pub unsafe extern "C" fn channel_find(buf: *const u8, size: usize) -> u64 {
    let mut data = Vec::with_capacity(size as usize);
    std::ptr::copy_nonoverlapping(buf, data.as_mut_ptr(), size as usize);
    data.set_len(size as usize);
    let port_name = String::from_utf8(data).unwrap();
    RUNTIME.with(|runtime| {
        *runtime.borrow().nodes["app"]
            .ports
            .get(&port_name)
            .unwrap_or(&0)
    })
}

/// Test-only placeholder for random data generation.
#[no_mangle]
pub unsafe extern "C" fn random_get(buf: *mut u8, size: usize) -> u32 {
    let mut rng = rand::thread_rng();
    for i in 0..size as isize {
        *(buf.offset(i)) = rng.gen::<u8>();
    }
    OakStatus::OK.value() as u32
}

// Test helper functions that allow Node unit test code to manipulate
// the mock Oak environment.

/// Test helper to add a port name referring to a handle.
pub fn add_port_name(name: &str, handle: oak::Handle) {
    RUNTIME.with(|runtime| {
        runtime
            .borrow_mut()
            .nodes
            .get_mut("app")
            .unwrap()
            .ports
            .insert(name.to_string(), handle);
    })
}

/// Convenience test helper to get a new write channel handle.
pub fn write_handle() -> oak::Handle {
    RUNTIME.with(|runtime| {
        let (write_handle, read_handle) = runtime.borrow_mut().node_channel_create("app");
        channel_close(read_handle);
        write_handle
    })
}

/// Convenience test helper to get a new read channel handle.
pub fn read_handle() -> oak::Handle {
    RUNTIME.with(|runtime| {
        let (write_handle, read_handle) = runtime.borrow_mut().node_channel_create("app");
        channel_close(write_handle);
        read_handle
    })
}

/// Convenience test helper which returns the last message on a channel as a
/// string (without removing it from the channel).
pub fn last_message_as_string(handle: oak::Handle) -> String {
    RUNTIME.with(|runtime| {
        let half = *runtime.borrow().nodes["app"].halves.get(&handle).unwrap();
        match runtime.borrow().channels[half.channel_idx].messages.front() {
            Some(msg) => unsafe { std::str::from_utf8_unchecked(&msg.data).to_string() },
            None => "".to_string(),
        }
    })
}

/// Test helper that injects a failure for future channel read operations.
pub fn set_read_status(handle: oak::Handle, status: Option<u32>) {
    RUNTIME.with(|runtime| {
        let half = *runtime.borrow().nodes["app"].halves.get(&handle).unwrap();
        runtime.borrow_mut().channels[half.channel_idx].read_status = status;
    })
}

/// Test helper that injects a failure for future channel write operations.
pub fn set_write_status(handle: oak::Handle, status: Option<u32>) {
    RUNTIME.with(|runtime| {
        let half = *runtime.borrow().nodes["app"].halves.get(&handle).unwrap();
        runtime.borrow_mut().channels[half.channel_idx].write_status = status;
    })
}

/// Test helper that clears any handle to channel half mappings.
pub fn reset() {
    RUNTIME.with(|runtime| runtime.borrow_mut().reset())
}

static LOG_INIT: Once = Once::new();

/// Test helper to initialize logging via simple_logger.
pub fn init_logging() {
    LOG_INIT.call_once(|| {
        simple_logger::init().unwrap();
        info!("Logging via simple_logger initialized");
    });
}

/// Test helper to mark the Application under test as pending termination.
pub fn set_termination_pending(val: bool) {
    RUNTIME.with(|runtime| {
        runtime.borrow_mut().termination_pending = val;
    });
}
