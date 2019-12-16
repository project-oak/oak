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

use lazy_static::lazy_static;
use log::{debug, info, warn};

use byteorder::{ReadBytesExt, WriteBytesExt};
use oak::OakStatus;
use proto::manager::NodeConfiguration_oneof_config_type;
use protobuf::{Message, ProtobufEnum};
use rand::Rng;
use std::cell::RefCell;
use std::collections::hash_map::{Entry, RandomState};
use std::collections::HashMap;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::io::Cursor;
use std::sync::{Arc, Once, RwLock};
use std::thread::spawn;

pub mod proto;
#[cfg(test)]
mod tests;

// Node name used for single-Node tests.
pub static DEFAULT_NODE_NAME: &str = "internal-0";

struct OakMessage {
    data: Vec<u8>,
    channels: Vec<ChannelHalf>,
}

#[derive(PartialEq, Copy, Clone, Debug, Eq, Hash)]
enum Direction {
    Read,
    Write,
}

/// Unidirectional message-based channel object that also allows fault
/// injection.
struct MockChannel {
    /// If read_status is set, this status value will be returned for any read
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    read_status: Option<u32>,
    /// If write_status is set, this status value will be returned for any write
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    write_status: Option<u32>,
    /// Track extant halves referring to this channel, so that it is possible to
    /// tell when a direction has been orphaned.
    half_count: HashMap<Direction, isize>,
    /// Pending messages on the channel
    messages: VecDeque<OakMessage>,
}

impl MockChannel {
    fn new() -> MockChannel {
        MockChannel {
            read_status: None,
            write_status: None,
            messages: VecDeque::new(),
            half_count: [(Direction::Read, 0), (Direction::Write, 0)]
                .iter()
                .cloned()
                .collect(),
        }
    }
    fn write_message(&mut self, msg: OakMessage) -> u32 {
        if let Some(status) = self.write_status {
            return status;
        }
        if self.half_count[&Direction::Read] == 0 {
            // Channel is orphaned; no-one can ever read this message.
            return OakStatus::ERR_CHANNEL_CLOSED.value() as u32;
        }
        self.messages.push_back(msg);
        OakStatus::OK.value() as u32
    }
    fn read_message(
        &mut self,
        size: usize,
        actual_size: &mut u32,
        handle_count: u32,
        actual_handle_count: &mut u32,
    ) -> Result<OakMessage, u32> {
        if let Some(status) = self.read_status {
            return Err(status);
        }
        match self.messages.pop_front() {
            None => {
                *actual_size = 0;
                *actual_handle_count = 0;
                if self.half_count[&Direction::Write] == 0 {
                    // Channel is empty and there can be no future writers, so
                    // indicate that the channel is closed.
                    Err(OakStatus::ERR_CHANNEL_CLOSED.value() as u32)
                } else {
                    Err(OakStatus::OK.value() as u32)
                }
            }
            Some(msg) => {
                // Check whether the message will fit within caller-specified limits; if
                // not, put it back on the queue (and return the required limits).
                *actual_size = msg.data.len() as u32;
                *actual_handle_count = msg.channels.len() as u32;
                if *actual_size > size as u32 {
                    self.messages.push_front(msg);
                    Err(OakStatus::ERR_BUFFER_TOO_SMALL.value() as u32)
                } else if *actual_handle_count > handle_count {
                    self.messages.push_front(msg);
                    Err(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL.value() as u32)
                } else {
                    Ok(msg)
                }
            }
        }
    }
}

type ChannelRef = Arc<RwLock<MockChannel>>;

// A channel half is a clonable reference to one half of a unidirectional channel.
struct ChannelHalf {
    direction: Direction,
    channel: ChannelRef,
}

impl ChannelHalf {
    fn new(direction: Direction, channel: ChannelRef) -> ChannelHalf {
        // Update the referenced channel's counts of extant halves.
        *channel
            .write()
            .expect("corrupt channel ref")
            .half_count
            .get_mut(&direction)
            .expect("missing enum value in half_count") += 1;
        ChannelHalf { direction, channel }
    }
}

impl Clone for ChannelHalf {
    fn clone(&self) -> ChannelHalf {
        ChannelHalf::new(self.direction, self.channel.clone())
    }
}

impl Drop for ChannelHalf {
    fn drop(&mut self) {
        // Update the referenced channel's counts of extant halves.
        match self
            .channel
            .write()
            .expect("corrupt channel ref")
            .half_count
            .entry(self.direction)
        {
            Entry::Occupied(mut e) => {
                if *e.get() <= 0 {
                    panic!("negative channel ref count");
                }
                *e.get_mut() -= 1;
            }
            Entry::Vacant(_) => panic!("missing enum value in half_count"),
        };
    }
}

struct OakRuntime {
    termination_pending: bool,
    // Map name of Node config names to a test entrypoint function pointer.
    entrypoints: HashMap<String, NodeMain>,
    // Map name of Node config names to next index.
    next_index: HashMap<String, u32>,
    // Track a reference to the write half of the channel used for sending
    // gRPC requests in to the Application under test.
    grpc_in_half: Option<ChannelHalf>,
    // Node instances organized by internal Node name.
    nodes: HashMap<String, OakNode>,
}

struct OakNode {
    halves: HashMap<oak::Handle, ChannelHalf>,
    // Handle for a thread running the main loop for this node.
    thread_handle: Option<std::thread::JoinHandle<i32>>,
}

// Encapsulate the information needed to start a new per-Node thread.
struct NodeStartInfo {
    entrypoint: NodeMain,
    node_name: String,
    handle: oak::Handle,
}

impl OakRuntime {
    fn new(node_name: Option<&str>) -> OakRuntime {
        let mut nodes = HashMap::new();
        if let Some(node_name) = node_name {
            // Create a single Node with the given name.
            nodes.insert(node_name.to_string(), OakNode::new());
        }
        OakRuntime {
            termination_pending: false,
            entrypoints: HashMap::new(),
            next_index: HashMap::new(),
            grpc_in_half: None,
            nodes,
        }
    }

    fn termination_pending(&self) -> bool {
        self.termination_pending
    }
    fn set_termination_pending(&mut self, value: bool) {
        self.termination_pending = value;
    }

    fn entrypoint(&self, config: &str) -> Option<NodeMain> {
        self.entrypoints.get(config).copied()
    }

    fn next_node_name(&mut self, config: &str) -> String {
        let index = self.next_index.entry(config.to_string()).or_insert(0);
        let name = format!("{}-{}", config, *index);
        *index += 1;
        name
    }

    // Build a runtime that has Node and Channels set up according to the given
    // Application configuration. Returns a (node-name, entrypoint, handle)
    // tuple indicating the initial Node that should be started.
    fn configure(
        &mut self,
        config: proto::manager::ApplicationConfiguration,
        entrypoints: HashMap<String, NodeMain>,
    ) -> Option<(String, NodeMain, oak::Handle)> {
        self.set_termination_pending(false);
        self.nodes.clear();
        self.entrypoints = entrypoints;
        for node_config in config.get_node_configs() {
            match &node_config.config_type {
                None => {
                    panic!("Node config {} with no type", node_config.name);
                }
                Some(NodeConfiguration_oneof_config_type::log_config(_)) => {
                    self.entrypoints
                        .insert(node_config.name.clone(), log_node_main);
                }
                Some(NodeConfiguration_oneof_config_type::wasm_config(_)) => {
                    // Check that we have an entrypoint corresponding to this.
                    if !self.entrypoints.contains_key(&node_config.name) {
                        panic!(
                            "no entrypoint provided for Node config {}",
                            node_config.name
                        )
                    }
                }
                Some(NodeConfiguration_oneof_config_type::storage_config(_storage_config)) => {
                    // TODO: Implement a storage pseudo-Node
                }
            }
        }
        let entrypoint = self.entrypoint(&config.initial_node)?;

        let node_name = self.next_node_name(&config.initial_node);
        let mut node = OakNode::new();
        debug!(
            "{{{}}}: add Wasm node running config '{}'",
            node_name, config.initial_node
        );

        // Setup the initial channel from gRPC pseudo-Node to Node.
        let channel = self.new_channel();
        self.grpc_in_half = Some(ChannelHalf::new(Direction::Write, channel.clone()));
        let half = ChannelHalf::new(Direction::Read, channel.clone());
        let handle = node.add_half(half);
        self.nodes.insert(node_name.clone(), node);

        Some((node_name, entrypoint, handle))
    }
    // Record that a Node of the given name has been started in a distinct thread.
    fn node_started(&mut self, node_name: &str, join_handle: std::thread::JoinHandle<i32>) {
        self.nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name))
            .thread_handle
            .replace(join_handle);
    }
    fn stop_next(&mut self) -> Option<(String, std::thread::JoinHandle<i32>)> {
        for (name, node) in &mut self.nodes {
            if let Some(h) = node.thread_handle.take() {
                return Some((name.to_string(), h));
            }
        }
        None
    }
    fn reset(&mut self) {
        for node in self.nodes.values_mut() {
            node.halves.clear();
        }
        self.grpc_in_half = None;
    }
    fn new_channel(&mut self) -> ChannelRef {
        Arc::new(RwLock::new(MockChannel::new()))
    }
    fn node_half_for_handle(&self, node_name: &str, handle: oak::Handle) -> Option<ChannelHalf> {
        let node = self.nodes.get(node_name)?;
        let half = node.halves.get(&handle)?;
        Some(half.clone())
    }
    fn node_half_for_handle_dir(
        &self,
        node_name: &str,
        handle: oak::Handle,
        dir: Direction,
    ) -> Option<ChannelHalf> {
        let half = self.node_half_for_handle(node_name, handle)?;
        if half.direction != dir {
            return None;
        }
        Some(half)
    }
    fn node_add_half(&mut self, node_name: &str, half: ChannelHalf) -> oak::Handle {
        self.nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name))
            .add_half(half)
    }
    fn node_channel_create(&mut self, node_name: &str) -> (oak::Handle, oak::Handle) {
        let channel = self.new_channel();
        let write_half = ChannelHalf::new(Direction::Write, channel.clone());
        let read_half = ChannelHalf::new(Direction::Read, channel.clone());
        let node = self
            .nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        (node.add_half(write_half), node.add_half(read_half))
    }
    fn node_channel_close(&mut self, node_name: &str, handle: oak::Handle) -> u32 {
        let node = self
            .nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        node.close_channel(handle)
    }
    fn node_channel_write(&mut self, node_name: &str, handle: oak::Handle, msg: OakMessage) -> u32 {
        match self.node_half_for_handle_dir(node_name, handle, Direction::Write) {
            None => oak::OakStatus::ERR_BAD_HANDLE.value() as u32,
            Some(half) => half
                .channel
                .write()
                .expect("corrupt channel ref")
                .write_message(msg),
        }
    }
    fn node_channel_read(
        &mut self,
        node_name: &str,
        handle: oak::Handle,
        size: usize,
        actual_size: &mut u32,
        handle_count: u32,
        actual_handle_count: &mut u32,
    ) -> Result<OakMessage, u32> {
        match self.node_half_for_handle_dir(node_name, handle, Direction::Read) {
            None => Err(oak::OakStatus::ERR_BAD_HANDLE.value() as u32),
            Some(half) => half
                .channel
                .write()
                .expect("corrupt channel ref")
                .read_message(size, actual_size, handle_count, actual_handle_count),
        }
    }
    fn node_channel_status(&self, node_name: &str, handle: oak::Handle) -> oak::ChannelReadStatus {
        match self.node_half_for_handle_dir(node_name, handle, Direction::Read) {
            None => oak::ChannelReadStatus::INVALID_CHANNEL,
            Some(half) => {
                let channel = half.channel.read().expect("corrupt channel ref");
                if !channel.messages.is_empty() {
                    oak::ChannelReadStatus::READ_READY
                } else if channel.half_count[&Direction::Write] == 0 {
                    oak::ChannelReadStatus::ORPHANED
                } else {
                    oak::ChannelReadStatus::NOT_READY
                }
            }
        }
    }
    fn grpc_channel_setup(&mut self, node_name: &str) -> oak::Handle {
        let channel = self.new_channel();
        let half = ChannelHalf::new(Direction::Read, channel.clone());
        let node = self
            .nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        let read_handle = node.add_half(half);
        debug!(
            "set up gRPC channel to node {} with handle {}",
            node_name, read_handle
        );
        // Remember the write half of the channel to allow future test
        // injection of gRPC requests.
        self.grpc_in_half = Some(ChannelHalf::new(Direction::Write, channel));
        read_handle
    }
    fn grpc_channel(&self) -> Option<ChannelRef> {
        let half = self.grpc_in_half.as_ref()?;
        Some(half.channel.clone())
    }
    fn node_create(
        &mut self,
        node_name: String,
        config: &str,
        handle: oak::Handle,
    ) -> Result<NodeStartInfo, OakStatus> {
        // First, find the code referred to by the config name.
        let entrypoint = match self.entrypoint(&config) {
            Some(e) => e,
            None => {
                debug!(
                    "{{{}}}: node_create('{}', {}) -> ERR_INVALID_ARGS",
                    node_name, config, handle
                );
                return Err(OakStatus::ERR_INVALID_ARGS);
            }
        };

        // Next, convert the creating Node's handle to a channel reference.
        let half = match self.node_half_for_handle_dir(&node_name, handle, Direction::Read) {
            Some(h) => h,
            None => {
                debug!(
                    "{{{}}}: node_create('{}', {}) -> ERR_BAD_HANDLE",
                    node_name, config, handle
                );
                return Err(OakStatus::ERR_BAD_HANDLE);
            }
        };

        // Create the new Node instance.
        let new_node_name = self.next_node_name(&config);
        let node = OakNode::new();
        debug!(
            "{{{}}}: add node running config '{}'",
            new_node_name, config
        );
        self.nodes.insert(new_node_name.to_string(), node);

        // Map the channel into the new Node's handle space.
        let new_handle = self.node_add_half(&new_node_name, half);

        // Return enough information to allow the new Node to be started:
        // entrypoint, name and initial handle value.
        Ok(NodeStartInfo {
            entrypoint,
            node_name: new_node_name,
            handle: new_handle,
        })
    }
}

impl OakNode {
    fn new() -> OakNode {
        OakNode {
            halves: HashMap::new(),
            thread_handle: None,
        }
    }
    fn next_handle(&self) -> oak::Handle {
        let mut rng = rand::thread_rng();
        loop {
            // Keep picking random Handle values until we find an unused (and valid) value.
            let handle = rng.gen::<oak::Handle>();
            if handle == oak::wasm::INVALID_HANDLE {
                continue;
            }
            if !self.halves.contains_key(&handle) {
                return handle;
            }
        }
    }
    fn add_half(&mut self, half: ChannelHalf) -> oak::Handle {
        let handle = self.next_handle();
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
// This is a mutable global (!) because the code under test expects to find
// global entrypoints corresponding to the Oak TCB, and there's no other way to
// get at the relevant associated state.
lazy_static! {
    static ref RUNTIME: RwLock<OakRuntime> = RwLock::new(OakRuntime::new(Some(DEFAULT_NODE_NAME)));
}

const RUNTIME_MISSING: &str = "global OakRuntime object missing";

// Per-thread Node name.
thread_local! {
    static NODE_NAME: RefCell<String> = RefCell::new(DEFAULT_NODE_NAME.to_string());
}

// Return a copy of the node name associated with the current thread.
fn node_name() -> String {
    NODE_NAME.with(|node_name| node_name.borrow().clone())
}

// Set the node name for the current thread.
fn set_node_name(name: String) {
    NODE_NAME.with(|node_name| node_name.replace(name));
}

// Implementations of the Oak API host functions in Rust for testing.
// These implementations generally handle the unsafe raw memory manipulation
// then forward on to the equivalent method on the current OakRuntime instance.

/// Declaration for the Node's main function.
extern "C" {
    pub fn oak_main(handle: u64) -> i32;
}

/// Test implementation of channel wait functionality, which always indicates
/// that all provided channels are ready for reading.
#[no_mangle]
pub unsafe extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> u32 {
    let name = node_name();
    debug!("{{{}}}: wait_on_channels({:?}, {})", name, buf, count);
    if count == 0 {
        debug!("{{{}}}: wait_on_channels() -> ERR_INVALID_ARGS", name);
        return OakStatus::ERR_INVALID_ARGS.value() as u32;
    }

    // Accumulate the handles we're interested in.
    let size = oak::wasm::SPACE_BYTES_PER_HANDLE * count as usize;
    let mut handle_data = Vec::<u8>::with_capacity(size);
    std::ptr::copy_nonoverlapping(buf, handle_data.as_mut_ptr(), size);
    handle_data.set_len(size);
    let mut handles = Vec::with_capacity(count as usize);
    let mut mem_reader = Cursor::new(handle_data);
    for _ in 0..count {
        let handle = mem_reader.read_u64::<byteorder::LittleEndian>().unwrap();
        let _b = mem_reader.read_u8().unwrap();
        handles.push(handle);
    }

    loop {
        // Check current handle status.
        let mut found_valid_handle = false;
        let mut found_ready_handle = false;
        for (i, handle) in handles.iter().enumerate() {
            let channel_status = RUNTIME
                .read()
                .expect(RUNTIME_MISSING)
                .node_channel_status(&name, *handle);
            if channel_status != oak::ChannelReadStatus::INVALID_CHANNEL {
                found_valid_handle = true;
            }
            if channel_status == oak::ChannelReadStatus::READ_READY {
                found_ready_handle = true;
            }

            // Write channel status back to the raw pointer.
            let p = buf.add(
                i * oak::wasm::SPACE_BYTES_PER_HANDLE + (oak::wasm::SPACE_BYTES_PER_HANDLE - 1),
            );
            *p = channel_status
                .value()
                .try_into()
                .expect("failed to convert status to u8");
        }
        if RUNTIME.read().expect(RUNTIME_MISSING).termination_pending() {
            debug!("{{{}}}: wait_on_channels() -> ERR_TERMINATED", name);
            return OakStatus::ERR_TERMINATED.value() as u32;
        }
        if found_ready_handle {
            debug!("{{{}}}: wait_on_channels() -> OK", name);
            return OakStatus::OK.value() as u32;
        }
        if !found_valid_handle {
            debug!("{{{}}}: wait_on_channels() -> ERR_BAD_HANDLE", name);
            return OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        // We have at least one valid handle but no pending data, so wait and try again.
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}

/// Test-only implementation of channel write functionality.
#[no_mangle]
pub unsafe extern "C" fn channel_write(
    handle: u64,
    buf: *const u8,
    size: usize,
    handle_buf: *const u8,
    handle_count: u32,
) -> u32 {
    let name = node_name();
    debug!(
        "{{{}}}: channel_write({}, {:?}, {}, {:?}, {})",
        name, handle, buf, size, handle_buf, handle_count
    );
    let mut msg = OakMessage {
        data: Vec::with_capacity(size),
        channels: Vec::with_capacity(handle_count as usize),
    };
    std::ptr::copy_nonoverlapping(buf, msg.data.as_mut_ptr(), size);
    msg.data.set_len(size);

    let handle_size = 8 * handle_count as usize;
    let mut handle_data = Vec::<u8>::with_capacity(handle_size);
    std::ptr::copy_nonoverlapping(handle_buf, handle_data.as_mut_ptr(), handle_size);
    handle_data.set_len(handle_size);

    let mut mem_reader = Cursor::new(handle_data);
    for _ in 0..handle_count as isize {
        let handle = mem_reader.read_u64::<byteorder::LittleEndian>().unwrap();
        let half = RUNTIME
            .read()
            .expect(RUNTIME_MISSING)
            .node_half_for_handle(&name, handle);
        match half {
            Some(half) => msg.channels.push(half),
            None => return OakStatus::ERR_BAD_HANDLE.value() as u32,
        }
    }

    let result = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_channel_write(&name, handle, msg);
    debug!("{{{}}}: channel_write() -> {}", name, result);
    result
}

/// Test implementation of channel read functionality, which reads a message
/// from the test channel.
#[no_mangle]
pub unsafe extern "C" fn channel_read(
    handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    handle_buf: *mut u8,
    handle_count: u32,
    actual_handle_count: *mut u32,
) -> u32 {
    let name = node_name();
    debug!(
        "{{{}}}: channel_read({}, {:?}, {}, {:?}, {:?}, {}, {:?})",
        name, handle, buf, size, actual_size, handle_buf, handle_count, actual_handle_count
    );
    let mut asize = 0u32;
    let mut acount = 0u32;
    let result = RUNTIME.write().expect(RUNTIME_MISSING).node_channel_read(
        &name,
        handle,
        size,
        &mut asize,
        handle_count,
        &mut acount,
    );
    *actual_size = asize;
    *actual_handle_count = acount;
    let msg = match result {
        Err(status) => {
            debug!("{{{}}}: channel_read() -> Err {}", name, status);
            return status;
        }
        Ok(msg) => msg,
    };
    std::ptr::copy_nonoverlapping(msg.data.as_ptr(), buf, asize as usize);
    let mut handle_data = Vec::with_capacity(8 * msg.channels.len());
    for half in msg.channels {
        let handle = RUNTIME
            .write()
            .expect(RUNTIME_MISSING)
            .node_add_half(&name, half);
        debug!("{{{}}}: channel_read() added handle {}", name, handle);
        handle_data
            .write_u64::<byteorder::LittleEndian>(handle)
            .unwrap();
    }
    std::ptr::copy_nonoverlapping(handle_data.as_ptr(), handle_buf, handle_data.len());

    debug!("{{{}}}: channel_read() -> OK", name);
    oak::OakStatus::OK as u32
}

/// Test version of channel creation.
#[no_mangle]
pub unsafe extern "C" fn channel_create(write: *mut u64, read: *mut u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: channel_create({:?}, {:?})", name, write, read);
    let (write_handle, read_handle) = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_channel_create(&name);

    *write = write_handle;
    *read = read_handle;
    debug!(
        "{{{}}}: channel_create(*w={}, *r={}) -> OK",
        name, write_handle, read_handle
    );
    OakStatus::OK.value() as u32
}

/// Test version of channel closure.
#[no_mangle]
pub extern "C" fn channel_close(handle: u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: channel_close({})", name, handle);
    let result = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_channel_close(&name, handle);
    debug!("{{{}}}: channel_close({}) -> {}", name, handle, result);
    result
}

/// Test implementation of dynamic Node creation.
#[no_mangle]
pub unsafe fn node_create(buf: *const u8, len: usize, handle: u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: node_create({:?}, {}, {})", name, buf, len, handle);
    let mut data = Vec::with_capacity(len as usize);
    std::ptr::copy_nonoverlapping(buf, data.as_mut_ptr(), len as usize);
    data.set_len(len as usize);
    let config = match String::from_utf8(data) {
        Err(_) => return OakStatus::ERR_INVALID_ARGS.value() as u32,
        Ok(s) => s,
    };
    debug!("{{{}}}: node_create('{}', {})", name, config, handle);

    let start_info = match RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_create(name, &config, handle)
    {
        Err(status) => return status.value() as u32,
        Ok(result) => result,
    };

    debug!(
        "{{{}}}: start per-Node thread with handle {}",
        start_info.node_name, start_info.handle
    );
    let node_name_copy = start_info.node_name.to_string();
    let thread_handle = spawn(move || {
        set_node_name(start_info.node_name);
        (start_info.entrypoint)(start_info.handle)
    });
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_started(&node_name_copy, thread_handle);

    OakStatus::OK.value() as u32
}

/// Test version of random data generation.
#[no_mangle]
pub unsafe extern "C" fn random_get(buf: *mut u8, size: usize) -> u32 {
    let name = node_name();
    debug!("{{{}}}: random_get({:?}, {})", name, buf, size);
    let mut rng = rand::thread_rng();
    for i in 0..size as isize {
        *(buf.offset(i)) = rng.gen::<u8>();
    }
    debug!("{{{}}}: random_get() -> OK", name);
    OakStatus::OK.value() as u32
}

// Test helper functions that allow Node unit test code to manipulate
// the mock Oak environment.

/// Convenience test helper which returns the last message on a channel as a
/// string (without removing it from the channel).
pub fn last_message_as_string(handle: oak::Handle) -> String {
    let half = RUNTIME.read().expect(RUNTIME_MISSING).nodes[DEFAULT_NODE_NAME]
        .halves
        .get(&handle)
        .expect("invalid handle passed to test helper")
        .clone();
    let result = match half
        .channel
        .read()
        .expect("corrupt channel ref")
        .messages
        .front()
    {
        Some(msg) => unsafe { std::str::from_utf8_unchecked(&msg.data).to_string() },
        None => "".to_string(),
    };
    debug!("last message '{}'", result);
    result
}

/// Test helper that injects a failure for future channel read operations.
pub fn set_read_status(node_name: &str, handle: oak::Handle, status: Option<u32>) {
    let half = RUNTIME.read().expect(RUNTIME_MISSING).nodes[node_name]
        .halves
        .get(&handle)
        .expect("invalid handle passed to test helper")
        .clone();
    half.channel
        .write()
        .expect("corrupt channel ref")
        .read_status = status;
}

/// Test helper that injects a failure for future channel write operations.
pub fn set_write_status(node_name: &str, handle: oak::Handle, status: Option<u32>) {
    let half = RUNTIME.read().expect(RUNTIME_MISSING).nodes[node_name]
        .halves
        .get(&handle)
        .expect("invalid handle passed to test helper")
        .clone();
    half.channel
        .write()
        .expect("corrupt channel ref")
        .write_status = status;
}

/// Test helper that clears any handle to channel half mappings.
pub fn reset() {
    RUNTIME.write().expect(RUNTIME_MISSING).reset()
}

static LOG_INIT: Once = Once::new();

/// Test helper to initialize logging via simple_logger.
pub fn init_logging() {
    LOG_INIT.call_once(|| {
        simple_logger::init().unwrap();
        info!("Logging via simple_logger initialized");
    });
}

/// Expected type for the main entrypoint to a Node under test.
pub type NodeMain = fn(u64) -> i32;

/// Start running the Application under test, with the given initial Node and
/// channel configuration.  Because multiple Nodes are linked into the same
/// test, the Nodes should be configured *not* to define the global extern "C"
/// oak_main(), as this would lead to duplicate symbols.  Instead, the
/// entrypoints map should provide a function pointer for each WasmConfiguration
/// entry in the configuration.
///
/// Also, Nodes under test should ensure that the oak_log crate does not end
/// being used for logging during tests, either by not calling oak_log::init()
/// at start-of-day (e.g. based on a build configuration), or by calling
/// oak_tests::init_logging() first, and ignoring the subsequent failure from
/// oak_log::init().
pub fn start(
    config: proto::manager::ApplicationConfiguration,
    entrypoints: HashMap<String, NodeMain, RandomState>,
) -> Option<()> {
    let (name, entrypoint, handle) = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .configure(config, entrypoints)?;
    debug!("{{{}}}: start per-Node thread", name);
    let node_name = name.clone();
    let thread_handle = spawn(move || {
        set_node_name(node_name);
        entrypoint(handle)
    });
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_started(&name, thread_handle);
    Some(())
}

/// Start running a test of a single-Node Application.  This assumes that the
/// single Node's main entrypoint is available as a global extern "C"
/// oak_main(), as for a live version of the Application.
pub fn start_node(handle: oak::Handle) {
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .set_termination_pending(false);
    debug!("start per-Node thread with handle {}", handle);
    let node_name = DEFAULT_NODE_NAME.to_string();
    let main_handle = spawn(move || unsafe {
        set_node_name(node_name);
        oak_main(handle)
    });
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_started(DEFAULT_NODE_NAME, main_handle)
}

/// Stop the running Application under test.
pub fn stop() -> OakStatus {
    info!("stop all running Node threads");
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .set_termination_pending(true);

    let mut overall_result = OakStatus::OK;
    loop {
        let (name, thread_handle) = match RUNTIME.write().expect(RUNTIME_MISSING).stop_next() {
            None => break,
            Some(x) => x,
        };
        debug!("{{{}}}: await thread join", name);
        let result = match OakStatus::from_i32(thread_handle.join().unwrap() as i32) {
            Some(status) => status,
            None => OakStatus::OAK_STATUS_UNSPECIFIED,
        };
        debug!("{{{}}}: thread result {}", name, result.value());
        if overall_result == OakStatus::OK || result == OakStatus::ERR_TERMINATED {
            // If any Node was terminated, treat the whole application as terminated.
            // Otherwise, take the first non-OK result from a Node.
            overall_result = result;
        }
    }
    reset();
    overall_result
}

// Main loop function for a log pseudo-Node.
fn log_node_main(handle: u64) -> i32 {
    if handle == oak::wasm::INVALID_HANDLE {
        return OakStatus::ERR_BAD_HANDLE.value();
    }
    let half = oak::ReadHandle { handle };
    loop {
        if let Err(status) = oak::wait_on_channels(&[half]) {
            return status.value();
        }
        let mut buf = Vec::<u8>::with_capacity(1024);
        let mut handles = Vec::with_capacity(8);
        oak::channel_read(half, &mut buf, &mut handles);
        if buf.is_empty() {
            debug!("no pending message; poll again");
            continue;
        }
        let message = String::from_utf8_lossy(&buf);
        info!("LOG: {}", message);
    }
}

/// Test helper to set up a channel into the (single) Node under test for
/// injected gRPC requests.
pub fn grpc_channel_setup_default() -> oak::Handle {
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .grpc_channel_setup(DEFAULT_NODE_NAME)
}

/// Test helper to inject a (single) gRPC request message to the Node
/// under test, and collect a (single) response.
pub fn inject_grpc_request<R, Q>(method_name: &str, req: R) -> oak::grpc::Result<Q>
where
    R: protobuf::Message,
    Q: protobuf::Message,
{
    // Put the request in a GrpcRequest wrapper and serialize into a message.
    let mut grpc_req = oak::proto::grpc_encap::GrpcRequest::new();
    grpc_req.set_method_name(method_name.to_string());
    let mut any = protobuf::well_known_types::Any::new();
    if let Err(e) = req.write_to_writer(&mut any.value) {
        warn!("failed to serialize gRPC request: {}", e);
        return Err(oak::grpc::build_status(
            oak::grpc::Code::INTERNAL,
            "failed to serialize gRPC request",
        ));
    }
    grpc_req.set_req_msg(any);
    grpc_req.set_last(true);
    let mut msg = OakMessage {
        data: Vec::new(),
        channels: Vec::new(),
    };
    grpc_req
        .write_to_writer(&mut msg.data)
        .expect("failed to serialize GrpcRequest message");

    // Create a new channel for the response to arrive on and attach to the message.
    let channel = RUNTIME.write().expect(RUNTIME_MISSING).new_channel();
    msg.channels
        .push(ChannelHalf::new(Direction::Write, channel.clone()));
    let read_half = ChannelHalf::new(Direction::Read, channel);

    // Send the message (with attached write handle) into the Node under test.
    let grpc_channel = RUNTIME
        .read()
        .expect(RUNTIME_MISSING)
        .grpc_channel()
        .expect("no gRPC channel setup");
    grpc_channel
        .write()
        .expect("corrupt gRPC channel ref")
        .write_message(msg);

    // Read the serialized, encapsulated response.
    loop {
        let mut size = 0u32;
        let mut count = 0u32;
        let result = read_half
            .channel
            .write()
            .expect("corrupt channel ref")
            .read_message(std::usize::MAX, &mut size, std::u32::MAX, &mut count);
        let rsp = match result {
            Err(e) => {
                if e == OakStatus::OK.value() as u32 {
                    info!("no pending gRPC response message; poll again soon");
                    std::thread::sleep(std::time::Duration::from_millis(100));
                    continue;
                } else {
                    panic!(format!("failed to read from response channel: {}", e));
                }
            }
            Ok(r) => r,
        };
        if rsp.data.is_empty() {
            info!("no pending message; poll again soon");
            std::thread::sleep(std::time::Duration::from_millis(100));
            continue;
        }
        let mut rsp: oak::proto::grpc_encap::GrpcResponse =
            protobuf::parse_from_bytes(&rsp.data).expect("failed to parse GrpcResponse message");
        if !rsp.last {
            panic!("Expected single final response");
        }

        if rsp.get_status().code != oak::grpc::Code::OK.value() {
            return Err(rsp.take_status());
        }
        let rsp: Q = protobuf::parse_from_bytes(&rsp.get_rsp_msg().value)
            .expect("Failed to parse response protobuf message");
        return Ok(rsp);
    }
}
