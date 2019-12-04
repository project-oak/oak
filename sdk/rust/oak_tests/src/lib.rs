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
use log::{debug, info};

use byteorder::{ReadBytesExt, WriteBytesExt};
use oak::OakStatus;
use proto::manager::Node_oneof_node_type;
use protobuf::{Message, ProtobufEnum};
use rand::Rng;
use std::cell::RefCell;
use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::io::Cursor;
use std::sync::{Arc, Once, RwLock};
use std::thread::spawn;

pub mod proto;
#[cfg(test)]
mod tests;

pub static DEFAULT_NODE_NAME: &str = "app";

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
        let msg = self.messages.pop_front();
        if msg.is_none() {
            *actual_size = 0;
            *actual_handle_count = 0;
            if self.half_count[&Direction::Write] == 0 {
                // Channel is empty and there can be no future writers, so
                // indicate that the channel is closed.
                return Err(OakStatus::ERR_CHANNEL_CLOSED.value() as u32);
            } else {
                return Err(OakStatus::OK.value() as u32);
            }
        }
        // Check whether the message will fit within caller-specified limits; if
        // not, put it back on the queue (and return the required limits).
        let msg = msg.unwrap();
        *actual_size = msg.data.len() as u32;
        *actual_handle_count = msg.channels.len() as u32;
        if *actual_size > size as u32 {
            self.messages.push_front(msg);
            return Err(OakStatus::ERR_BUFFER_TOO_SMALL.value() as u32);
        }
        if *actual_handle_count > handle_count {
            self.messages.push_front(msg);
            return Err(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL.value() as u32);
        }
        Ok(msg)
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
            .unwrap()
            .half_count
            .get_mut(&direction)
            .unwrap() += 1;
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
        *self
            .channel
            .write()
            .unwrap()
            .half_count
            .get_mut(&self.direction)
            .unwrap() -= 1;
        assert!(self.channel.read().unwrap().half_count[&self.direction] >= 0);
    }
}

struct OakRuntime {
    termination_pending: bool,
    // Map name of Wasm contents to a test entrypoint function pointer.
    entrypoints: HashMap<String, NodeMain>,
    // Map name of Wasm contents to next index.
    next_index: HashMap<String, u32>,
    // Track a reference to the write half of the channel used for sending
    // gRPC requests in to the Application under test.
    grpc_in_half: Option<ChannelHalf>,
    // Node instances organized by Node name.
    nodes: HashMap<String, OakNode>,
}

struct OakNode {
    contents_name: String,
    halves: HashMap<oak::Handle, ChannelHalf>,
    // Mapping from port name to channel handle, as induced by the Application
    // configuration.
    ports: HashMap<String, oak::Handle>,
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
    fn new() -> OakRuntime {
        let mut nodes = HashMap::new();
        // For convenience, assume a single-Node application with the default
        // name for that Node.
        nodes.insert(DEFAULT_NODE_NAME.to_string(), OakNode::new());
        OakRuntime {
            termination_pending: false,
            entrypoints: HashMap::new(),
            next_index: HashMap::new(),
            grpc_in_half: None,
            nodes,
        }
    }

    fn entrypoint(&self, contents: &str) -> Option<NodeMain> {
        self.entrypoints.get(contents).copied()
    }

    fn next_node_name(&mut self, contents: &str) -> String {
        let index = self.next_index.entry(contents.to_string()).or_insert(0);
        let name = format!("{}-{}", contents, *index);
        *index += 1;
        name
    }

    // Build a runtime that has Node and Channels set up according to the given
    // Application configuration. Returns a vector of (node-name, entrypoint)
    // pairs indicating which Nodes need to be started, running which code.
    fn configure(
        &mut self,
        config: proto::manager::ApplicationConfiguration,
        entrypoints: HashMap<String, NodeMain>,
    ) -> Vec<(String, NodeMain)> {
        // TODO: validate the config
        let mut required_nodes = Vec::new();
        self.termination_pending = false;
        self.entrypoints = entrypoints;
        self.nodes.clear();
        let mut grpc_node_name: Option<&str> = None;
        let mut log_node_name: Option<&str> = None;
        let mut log_channel: Option<ChannelRef> = None;
        for node_cfg in config.get_nodes() {
            if let Some(Node_oneof_node_type::web_assembly_node(wasm_cfg)) = &node_cfg.node_type {
                let mut node = OakNode::new();
                node.contents_name = wasm_cfg.wasm_contents_name.clone();
                debug!(
                    "{{{}}}: add Wasm node running content '{}'",
                    node_cfg.node_name, wasm_cfg.wasm_contents_name
                );
                self.nodes.insert(node_cfg.node_name.to_string(), node);
                let entrypoint = self
                    .entrypoint(&wasm_cfg.wasm_contents_name)
                    .unwrap_or_else(|| {
                        panic!("failed to find {} entrypoint", wasm_cfg.wasm_contents_name)
                    });
                required_nodes.push((node_cfg.node_name.clone(), entrypoint));
            } else if let Some(Node_oneof_node_type::grpc_server_node(_)) = node_cfg.node_type {
                debug!("{{{}}}: add gRPC pseudo-Node", node_cfg.node_name);
                grpc_node_name = Some(&node_cfg.node_name);
            } else if let Some(Node_oneof_node_type::log_node(_)) = node_cfg.node_type {
                let node = OakNode::new();
                log_node_name = Some(&node_cfg.node_name);
                debug!("{{{}}}: add log pseudo-Node", node_cfg.node_name);
                self.nodes.insert(node_cfg.node_name.to_string(), node);
                required_nodes.push((node_cfg.node_name.to_string(), log_node_main));
            }
            // TODO: add storage support
        }
        for channel_cfg in config.get_channels() {
            let src = channel_cfg.get_source_endpoint();
            let dest = channel_cfg.get_destination_endpoint();
            debug!(
                "add channel {{{}}}:{} -> {{{}}}:{}",
                src.node_name, src.port_name, dest.node_name, dest.port_name
            );
            let channel = if log_node_name.is_some()
                && dest.node_name == log_node_name.unwrap()
                && dest.port_name == oak_log::IN_PORT_NAME
            {
                if log_channel.is_none() {
                    log_channel = Some(self.new_channel());
                }
                log_channel.clone().unwrap()
            } else {
                self.new_channel()
            };

            if grpc_node_name.is_some()
                && src.node_name == grpc_node_name.unwrap()
                && src.port_name == oak::grpc::OUT_PORT_NAME
            {
                debug!("channel is gRPC input channel");
                self.grpc_in_half = Some(ChannelHalf::new(Direction::Write, channel.clone()));
            }
            if self.nodes.contains_key(&src.node_name) {
                let half = ChannelHalf::new(Direction::Write, channel.clone());
                self.nodes
                    .get_mut(&src.node_name)
                    .unwrap()
                    .add_named_half(half, &src.port_name);
            }
            if self.nodes.contains_key(&dest.node_name) {
                let half = ChannelHalf::new(Direction::Read, channel.clone());
                self.nodes
                    .get_mut(&dest.node_name)
                    .unwrap()
                    .add_named_half(half, &dest.port_name);
            }
        }
        required_nodes
    }
    // Record that a Node of the given name has been started in a distinct thread.
    fn started(&mut self, node_name: &str, join_handle: std::thread::JoinHandle<i32>) {
        self.nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name))
            .thread_handle
            .replace(join_handle);
    }
    fn stop_next(&mut self) -> Option<(String, std::thread::JoinHandle<i32>)> {
        for (name, node) in &mut self.nodes {
            if node.thread_handle.is_some() {
                return Some((name.to_string(), node.thread_handle.take().unwrap()));
            }
        }
        None
    }
    fn reset(&mut self) {
        let names: Vec<String> = self.nodes.keys().cloned().collect();
        for name in &names {
            let node = self.nodes.get_mut(name).unwrap();
            node.halves.clear();
            node.ports.clear();
        }
        self.grpc_in_half = None;
    }
    fn new_channel(&mut self) -> ChannelRef {
        Arc::new(RwLock::new(MockChannel::new()))
    }
    fn node_half_for_handle(&self, node_name: &str, handle: oak::Handle) -> Option<ChannelHalf> {
        let node = self.nodes.get(node_name).unwrap();
        if !node.halves.contains_key(&handle) {
            return None;
        }
        let half = node.halves.get(&handle).unwrap();
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
        self.nodes.get_mut(node_name).unwrap().add_half(half)
    }
    fn node_channel_create(&mut self, node_name: &str) -> (oak::Handle, oak::Handle) {
        let channel = self.new_channel();
        let write_half = ChannelHalf::new(Direction::Write, channel.clone());
        let read_half = ChannelHalf::new(Direction::Read, channel.clone());
        let node = self.nodes.get_mut(node_name).unwrap();
        (node.add_half(write_half), node.add_half(read_half))
    }
    fn node_channel_write(&mut self, node_name: &str, handle: oak::Handle, msg: OakMessage) -> u32 {
        let half = self.node_half_for_handle_dir(node_name, handle, Direction::Write);
        if half.is_none() {
            return oak::OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        half.unwrap().channel.write().unwrap().write_message(msg)
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
        let half = self.node_half_for_handle_dir(node_name, handle, Direction::Read);
        if half.is_none() {
            return Err(oak::OakStatus::ERR_BAD_HANDLE.value() as u32);
        }
        half.unwrap().channel.write().unwrap().read_message(
            size,
            actual_size,
            handle_count,
            actual_handle_count,
        )
    }
    fn channel_status_for_node(
        &self,
        node_name: &str,
        handle: oak::Handle,
    ) -> oak::ChannelReadStatus {
        let half = self.node_half_for_handle_dir(node_name, handle, Direction::Read);
        if half.is_none() {
            oak::ChannelReadStatus::INVALID_CHANNEL
        } else {
            let channel = half.as_ref().unwrap().channel.read().unwrap();
            if !channel.messages.is_empty() {
                oak::ChannelReadStatus::READ_READY
            } else if channel.half_count[&Direction::Write] == 0 {
                oak::ChannelReadStatus::ORPHANED
            } else {
                oak::ChannelReadStatus::NOT_READY
            }
        }
    }
    fn grpc_channel_setup(&mut self, node_name: &str, port_name: &str) {
        let channel = self.new_channel();
        let half = ChannelHalf::new(Direction::Read, channel.clone());
        let node = self.nodes.get_mut(node_name).unwrap();
        let read_handle = node.add_named_half(half, port_name);
        debug!(
            "set up '{}' channel to node {} with handle {}",
            port_name, node_name, read_handle
        );
        self.grpc_in_half = Some(ChannelHalf::new(Direction::Write, channel));
    }
    fn grpc_channel(&self) -> Option<ChannelRef> {
        let half = self.grpc_in_half.as_ref()?;
        Some(half.channel.clone())
    }
    fn node_create(
        &mut self,
        node_name: String,
        contents: &str,
        handle: oak::Handle,
    ) -> Result<NodeStartInfo, OakStatus> {
        // First, find the code referred to by the contents name.
        let entrypoint = match self.entrypoint(&contents) {
            Some(e) => e,
            None => {
                debug!(
                    "{{{}}}: node_create('{}', {}) -> ERR_INVALID_ARGS",
                    node_name, contents, handle
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
                    node_name, contents, handle
                );
                return Err(OakStatus::ERR_BAD_HANDLE);
            }
        };

        // Create the new Node instance.
        let new_node_name = self.next_node_name(&contents);
        let mut node = OakNode::new();
        node.contents_name = contents.to_string();
        debug!(
            "{{{}}}: add node running content '{}'",
            new_node_name, contents
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
            contents_name: "<default>".to_string(),
            halves: HashMap::new(),
            ports: HashMap::new(),
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
    fn add_named_half(&mut self, half: ChannelHalf, port_name: &str) -> oak::Handle {
        let handle = self.add_half(half);
        self.ports.insert(port_name.to_string(), handle);
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
    static ref RUNTIME: RwLock<OakRuntime> = RwLock::new(OakRuntime::new());
}

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

/// Test-only implementation of channel wait functionality, which always
/// indicates that all provided channels are ready for reading.
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
                .unwrap()
                .channel_status_for_node(&name, *handle);
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
            *p = channel_status.value().try_into().unwrap();
        }
        if RUNTIME.read().unwrap().termination_pending {
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
        let half = RUNTIME.read().unwrap().node_half_for_handle(&name, handle);
        match half {
            Some(half) => msg.channels.push(half),
            None => return OakStatus::ERR_BAD_HANDLE.value() as u32,
        }
    }

    let result = RUNTIME
        .write()
        .unwrap()
        .node_channel_write(&name, handle, msg);
    debug!("{{{}}}: channel_write() -> {}", name, result);
    result
}

/// Test-only implementation of channel read functionality, which reads a
/// message from the test channel.
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
    let result = RUNTIME.write().unwrap().node_channel_read(
        &name,
        handle,
        size,
        &mut asize,
        handle_count,
        &mut acount,
    );
    *actual_size = asize;
    *actual_handle_count = acount;
    if let Err(status) = result {
        debug!("{{{}}}: channel_read() -> Err {}", name, status);
        return status;
    }
    let msg = result.unwrap();
    std::ptr::copy_nonoverlapping(msg.data.as_ptr(), buf, asize as usize);
    let mut handle_data = Vec::with_capacity(8 * msg.channels.len());
    for half in msg.channels {
        let handle = RUNTIME.write().unwrap().node_add_half(&name, half);
        debug!("{{{}}}: channel_read() added handle {}", name, handle);
        handle_data
            .write_u64::<byteorder::LittleEndian>(handle)
            .unwrap();
    }
    std::ptr::copy_nonoverlapping(handle_data.as_ptr(), handle_buf, handle_data.len());

    debug!("{{{}}}: channel_read() -> OK", name);
    oak::OakStatus::OK as u32
}

/// Test-only version of channel creation.
#[no_mangle]
pub unsafe extern "C" fn channel_create(write: *mut u64, read: *mut u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: channel_create({:?}, {:?})", name, write, read);
    let (write_handle, read_handle) = RUNTIME.write().unwrap().node_channel_create(&name);

    *write = write_handle;
    *read = read_handle;
    debug!(
        "{{{}}}: channel_create(*w={}, *r={}) -> OK",
        name, write_handle, read_handle
    );
    OakStatus::OK.value() as u32
}

/// Test-only version of channel closure.
#[no_mangle]
pub extern "C" fn channel_close(handle: u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: channel_close({})", name, handle);
    let result = RUNTIME
        .write()
        .unwrap()
        .nodes
        .get_mut(&name)
        .unwrap()
        .close_channel(handle);
    debug!("{{{}}}: channel_close({}) -> {}", name, handle, result);
    result
}

/// Test-only placeholder for finding a channel by preconfigured port name.
#[no_mangle]
pub unsafe extern "C" fn channel_find(buf: *const u8, size: usize) -> u64 {
    let name = node_name();
    debug!("{{{}}}: channel_find({:?}, {})", name, buf, size);
    let mut data = Vec::with_capacity(size as usize);
    std::ptr::copy_nonoverlapping(buf, data.as_mut_ptr(), size as usize);
    data.set_len(size as usize);
    let port_name = String::from_utf8(data).unwrap();
    let handle = *RUNTIME.read().unwrap().nodes[&name]
        .ports
        .get(&port_name)
        .unwrap_or(&0);
    debug!("{{{}}}: channel_find('{}') -> {}", name, port_name, handle);
    handle
}

/// Test framework implementation of dynamic Node creation.
#[no_mangle]
pub unsafe fn node_create(buf: *const u8, len: usize, handle: u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: node_create({:?}, {})", name, buf, len);
    let mut data = Vec::with_capacity(len as usize);
    std::ptr::copy_nonoverlapping(buf, data.as_mut_ptr(), len as usize);
    data.set_len(len as usize);
    let contents = String::from_utf8(data).unwrap();
    debug!("{{{}}}: node_create('{}', {})", name, contents, handle);

    let start_info = match RUNTIME
        .write()
        .unwrap()
        .node_create(name, &contents, handle)
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
        .unwrap()
        .started(&node_name_copy, thread_handle);

    OakStatus::OK.value() as u32
}

/// Test-only placeholder for random data generation.
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

/// Test helper to add a port name referring to a handle.
pub fn add_port_name(name: &str, handle: oak::Handle) {
    debug!("registered port '{}' -> handle {}", name, handle);
    RUNTIME
        .write()
        .unwrap()
        .nodes
        .get_mut(DEFAULT_NODE_NAME)
        .unwrap()
        .ports
        .insert(name.to_string(), handle);
}

/// Convenience test helper which returns the last message on a channel as a
/// string (without removing it from the channel).
pub fn last_message_as_string(handle: oak::Handle) -> String {
    let half = RUNTIME.read().unwrap().nodes[DEFAULT_NODE_NAME]
        .halves
        .get(&handle)
        .unwrap()
        .clone();
    let result = match half.channel.read().unwrap().messages.front() {
        Some(msg) => unsafe { std::str::from_utf8_unchecked(&msg.data).to_string() },
        None => "".to_string(),
    };
    debug!("last message '{}'", result);
    result
}

/// Test helper that injects a failure for future channel read operations.
pub fn set_read_status(node_name: &str, handle: oak::Handle, status: Option<u32>) {
    let half = RUNTIME.read().unwrap().nodes[node_name]
        .halves
        .get(&handle)
        .unwrap()
        .clone();
    half.channel.write().unwrap().read_status = status;
}

/// Test helper that injects a failure for future channel write operations.
pub fn set_write_status(node_name: &str, handle: oak::Handle, status: Option<u32>) {
    let half = RUNTIME.read().unwrap().nodes[node_name]
        .halves
        .get(&handle)
        .unwrap()
        .clone();
    half.channel.write().unwrap().write_status = status;
}

/// Test helper that clears any handle to channel half mappings.
pub fn reset() {
    RUNTIME.write().unwrap().reset()
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
    RUNTIME.write().unwrap().termination_pending = val;
}

/// Expected type for the main entrypoint to a Node under test.
pub type NodeMain = fn(u64) -> i32;

/// Start running the Application under test, with the given initial Node and
/// channel configuration.  Because multiple Nodes are linked into the same
/// test, the Nodes should be configured *not* to define the global extern "C"
/// oak_main(), as this would lead to duplicate symbols.  Instead, the
/// entrypoints map should provide a function pointer for each WasmContents
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
) {
    let required_nodes = RUNTIME.write().unwrap().configure(config, entrypoints);
    for (name, entrypoint) in required_nodes {
        debug!("{{{}}}: start per-Node thread", name);
        let node_name = name.clone();
        let thread_handle = spawn(move || {
            set_node_name(node_name);
            // TODO: provide a valid handle.
            entrypoint(oak::wasm::INVALID_HANDLE)
        });
        RUNTIME.write().unwrap().started(&name, thread_handle);
    }
}

/// Start running a test of a single-Node Application.  This assumes that the
/// single Node's main entrypoint is available as a global extern "C"
/// oak_main(), as for a live version of the Application.
pub fn start_node(name: &str) {
    RUNTIME.write().unwrap().termination_pending = false;
    debug!("{{{}}}: start per-Node thread", name);
    let node_name = name.to_string();
    let main_handle = spawn(|| unsafe {
        set_node_name(node_name);
        // TODO: provide a valid handle.
        oak_main(oak::wasm::INVALID_HANDLE)
    });
    RUNTIME.write().unwrap().started(name, main_handle)
}

/// Stop the running Application under test.
pub fn stop() -> OakStatus {
    info!("stop all running Node threads");
    set_termination_pending(true);

    let mut overall_result = OakStatus::OK;
    loop {
        let next = RUNTIME.write().unwrap().stop_next();
        if next.is_none() {
            break;
        }
        let (name, thread_handle) = next.unwrap();
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
fn log_node_main(_handle: u64) -> i32 {
    let half = oak::ReadHandle {
        handle: oak::channel_find(oak_log::IN_PORT_NAME),
    };
    if half.handle == oak::wasm::INVALID_HANDLE {
        return OakStatus::ERR_BAD_HANDLE.value();
    }
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

/// Test helper to set up a channel into the Node under for injected gRPC
/// requests, using default parameters (node "app" port "grpc_in").
pub fn grpc_channel_setup_default() {
    grpc_channel_setup(DEFAULT_NODE_NAME, oak::grpc::DEFAULT_IN_PORT_NAME)
}

/// Test helper to set up a channel into a Node under for injected gRPC
/// requests.
pub fn grpc_channel_setup(node_name: &str, port_name: &str) {
    RUNTIME
        .write()
        .unwrap()
        .grpc_channel_setup(node_name, port_name)
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
    req.write_to_writer(&mut any.value).unwrap();
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
    let channel = RUNTIME.write().unwrap().new_channel();
    msg.channels
        .push(ChannelHalf::new(Direction::Write, channel.clone()));
    let read_half = ChannelHalf::new(Direction::Read, channel);

    // Send the message (with attached write handle) into the Node under test.
    let grpc_channel = RUNTIME
        .read()
        .unwrap()
        .grpc_channel()
        .expect("no gRPC channel setup");
    grpc_channel.write().unwrap().write_message(msg);

    // Read the serialized, encapsulated response.
    loop {
        let mut size = 0u32;
        let mut count = 0u32;
        let result = read_half.channel.write().unwrap().read_message(
            std::usize::MAX,
            &mut size,
            std::u32::MAX,
            &mut count,
        );
        if let Err(e) = result {
            if e == OakStatus::OK.value() as u32 {
                info!("no pending message; poll again soon");
                std::thread::sleep(std::time::Duration::from_millis(100));
                continue;
            } else {
                panic!(format!("failed to read from response channel: {}", e));
            }
        }
        let rsp = result.unwrap();
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
