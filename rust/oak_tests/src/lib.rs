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
extern crate byteorder;
extern crate protobuf;
extern crate rand;
#[macro_use]
extern crate lazy_static;

use byteorder::{ReadBytesExt, WriteBytesExt};
use oak::OakStatus;
use proto::manager::Node_oneof_node_type;
use protobuf::{Message, ProtobufEnum};
use rand::Rng;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::io::Cursor;
use std::sync::{Once, RwLock};
use std::thread::spawn;

pub mod proto;
#[cfg(test)]
mod tests;

pub static DEFAULT_NODE_NAME: &str = "app";

struct OakMessage {
    data: Vec<u8>,
    channels: Vec<ChannelHalf>,
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
            return Err(OakStatus::OK.value() as u32);
        }
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

impl ChannelHalf {
    fn new(direction: Direction, channel_idx: usize) -> ChannelHalf {
        ChannelHalf {
            direction,
            channel_idx,
        }
    }
}

struct OakRuntime {
    termination_pending: bool,
    grpc_channel_idx: Option<usize>,
    channels: Vec<MockChannel>,
    nodes: HashMap<String, OakNode>,
}

struct OakNode {
    next_handle: oak::Handle,
    contents_name: String,
    halves: HashMap<oak::Handle, ChannelHalf>,
    ports: HashMap<String, oak::Handle>,
    thread_handle: Option<std::thread::JoinHandle<i32>>,
}

impl OakRuntime {
    fn new() -> OakRuntime {
        let mut nodes = HashMap::new();
        // For convenience, assume a single-Node application with the default
        // name for that Node.
        nodes.insert(DEFAULT_NODE_NAME.to_string(), OakNode::new());
        OakRuntime {
            termination_pending: false,
            grpc_channel_idx: None,
            channels: Vec::new(),
            nodes,
        }
    }
    fn configure(
        &mut self,
        config: proto::manager::ApplicationConfiguration,
    ) -> Vec<(String, String)> {
        // TODO: validate the config
        let mut required_nodes = Vec::new();
        self.termination_pending = false;
        self.nodes.clear();
        let mut grpc_node_name: Option<&str> = None;
        for node_cfg in config.get_nodes() {
            if let Some(Node_oneof_node_type::web_assembly_node(wasm_cfg)) = &node_cfg.node_type {
                let mut node = OakNode::new();
                node.contents_name = wasm_cfg.wasm_contents_name.clone();
                debug!(
                    "{{{}}}: add Wasm node running content '{}'",
                    node_cfg.node_name, wasm_cfg.wasm_contents_name
                );
                self.nodes.insert(node_cfg.node_name.to_string(), node);
                required_nodes.push((
                    node_cfg.node_name.clone(),
                    wasm_cfg.wasm_contents_name.clone(),
                ));
            } else if let Some(Node_oneof_node_type::grpc_server_node(_)) = node_cfg.node_type {
                grpc_node_name = Some(&node_cfg.node_name);
            }
            // TODO: add storage support
        }
        for channel_cfg in config.get_channels() {
            let channel_idx = self.new_channel();
            let src = channel_cfg.get_source_endpoint();
            let dest = channel_cfg.get_destination_endpoint();
            debug!(
                "add channel {{{}}}:{} -> {{{}}}:{}",
                src.node_name, src.port_name, dest.node_name, dest.port_name
            );
            if grpc_node_name.is_some()
                && src.node_name == grpc_node_name.unwrap()
                && src.port_name == oak::grpc::OUT_PORT_NAME
            {
                debug!("channel {} is gRPC input channel", channel_idx);
                self.grpc_channel_idx = Some(channel_idx);
            }
            if self.nodes.contains_key(&src.node_name) {
                let half = ChannelHalf::new(Direction::Write, channel_idx);
                self.nodes
                    .get_mut(&src.node_name)
                    .unwrap()
                    .add_named_half(half, &src.port_name);
            }
            if self.nodes.contains_key(&dest.node_name) {
                let half = ChannelHalf::new(Direction::Read, channel_idx);
                self.nodes
                    .get_mut(&dest.node_name)
                    .unwrap()
                    .add_named_half(half, &dest.port_name);
            }
        }
        required_nodes
    }
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
        self.grpc_channel_idx = None;
    }
    fn new_channel(&mut self) -> usize {
        let channel_idx = self.channels.len();
        self.channels.push(MockChannel::new());
        channel_idx
    }
    fn node_half_for_handle(&self, node_name: &str, handle: oak::Handle) -> Option<ChannelHalf> {
        let node = self.nodes.get(node_name).unwrap();
        if !node.halves.contains_key(&handle) {
            return None;
        }
        let half = node.halves.get(&handle).unwrap();
        Some(*half)
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
        let channel_idx = self.new_channel();
        let write_half = ChannelHalf::new(Direction::Write, channel_idx);
        let read_half = ChannelHalf::new(Direction::Read, channel_idx);
        let node = self.nodes.get_mut(node_name).unwrap();
        (node.add_half(write_half), node.add_half(read_half))
    }
    fn node_channel_write(&mut self, node_name: &str, handle: oak::Handle, msg: OakMessage) -> u32 {
        let half = self.node_half_for_handle_dir(node_name, handle, Direction::Write);
        if half == None {
            return oak::OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        self.channel_write_internal(half.unwrap().channel_idx, msg)
    }
    // Internal variant that takes a global channel index rather than a per-Node
    // handle.
    fn channel_write_internal(&mut self, channel_idx: usize, msg: OakMessage) -> u32 {
        self.channels[channel_idx].write_message(msg)
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
        if half == None {
            return Err(oak::OakStatus::ERR_BAD_HANDLE.value() as u32);
        }
        self.channel_read_internal(
            half.unwrap().channel_idx,
            size,
            actual_size,
            handle_count,
            actual_handle_count,
        )
    }
    // Internal variant that takes a global channel index rather than a per-Node
    // handle.
    fn channel_read_internal(
        &mut self,
        channel_idx: usize,
        size: usize,
        actual_size: &mut u32,
        handle_count: u32,
        actual_handle_count: &mut u32,
    ) -> Result<OakMessage, u32> {
        self.channels[channel_idx].read_message(
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
        } else if self.channels[half.unwrap().channel_idx].messages.is_empty() {
            oak::ChannelReadStatus::NOT_READY
        } else {
            oak::ChannelReadStatus::READ_READY
        }
    }
    fn grpc_channel_setup(&mut self, node_name: &str, port_name: &str) {
        let channel_idx = self.new_channel();
        let half = ChannelHalf::new(Direction::Read, channel_idx);
        let node = self.nodes.get_mut(node_name).unwrap();
        let read_handle = node.add_named_half(half, port_name);
        debug!(
            "set up '{}' channel#{} to node {} with handle {}",
            port_name, channel_idx, node_name, read_handle
        );
        self.grpc_channel_idx = Some(channel_idx);
    }
}

impl OakNode {
    fn new() -> OakNode {
        OakNode {
            next_handle: 1 as oak::Handle,
            contents_name: "<default>".to_string(),
            halves: HashMap::new(),
            ports: HashMap::new(),
            thread_handle: None,
        }
    }
    fn add_half(&mut self, half: ChannelHalf) -> oak::Handle {
        let handle = self.next_handle;
        self.next_handle += 1;
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
    pub fn oak_main() -> i32;
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
            break;
        }
        if !found_valid_handle {
            debug!("{{{}}}: wait_on_channels() -> ERR_BAD_HANDLE", name);
            return OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        // We have at least one valid handle but no pending data, so wait and try again.
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    debug!("{{{}}}: wait_on_channels() -> OK", name);
    OakStatus::OK.value() as u32
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
    for _i in 0..handle_count as isize {
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

/// Convenience test helper to get a new write channel handle.
pub fn write_handle() -> oak::Handle {
    let (write_handle, read_handle) = RUNTIME
        .write()
        .unwrap()
        .node_channel_create(DEFAULT_NODE_NAME);
    channel_close(read_handle);
    write_handle
}

/// Convenience test helper to get a new read channel handle.
pub fn read_handle() -> oak::Handle {
    let (write_handle, read_handle) = RUNTIME
        .write()
        .unwrap()
        .node_channel_create(DEFAULT_NODE_NAME);
    channel_close(write_handle);
    read_handle
}

/// Convenience test helper which returns the last message on a channel as a
/// string (without removing it from the channel).
pub fn last_message_as_string(handle: oak::Handle) -> String {
    let half = *RUNTIME.read().unwrap().nodes[DEFAULT_NODE_NAME]
        .halves
        .get(&handle)
        .unwrap();
    match RUNTIME.read().unwrap().channels[half.channel_idx]
        .messages
        .front()
    {
        Some(msg) => unsafe { std::str::from_utf8_unchecked(&msg.data).to_string() },
        None => "".to_string(),
    }
}

/// Test helper that injects a failure for future channel read operations.
pub fn set_read_status(node_name: &str, handle: oak::Handle, status: Option<u32>) {
    let half = *RUNTIME.read().unwrap().nodes[node_name]
        .halves
        .get(&handle)
        .unwrap();
    RUNTIME.write().unwrap().channels[half.channel_idx].read_status = status;
}

/// Test helper that injects a failure for future channel write operations.
pub fn set_write_status(node_name: &str, handle: oak::Handle, status: Option<u32>) {
    let half = *RUNTIME.read().unwrap().nodes[node_name]
        .halves
        .get(&handle)
        .unwrap();
    RUNTIME.write().unwrap().channels[half.channel_idx].write_status = status;
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
pub type NodeMain = fn() -> i32;

/// Start running the Application under test, with the given initial Node
/// and channel configuration.  The entrypoints map should provide a function
/// pointer for each WasmContents entry in the configuration.
pub fn start<S: ::std::hash::BuildHasher>(
    config: proto::manager::ApplicationConfiguration,
    entrypoints: HashMap<String, NodeMain, S>,
) {
    let required_nodes = RUNTIME.write().unwrap().configure(config);
    for (name, contents_name) in required_nodes {
        debug!(
            "{{{}}}: start per-Node thread with contents '{}'",
            name, contents_name
        );
        let node_name = name.clone();
        let entrypoint = *entrypoints
            .get(&contents_name)
            .unwrap_or_else(|| panic!("failed to find {} entrypoint", contents_name));
        let thread_handle = spawn(move || {
            set_node_name(node_name);
            entrypoint()
        });
        RUNTIME.write().unwrap().started(&name, thread_handle);
    }
}

/// Start running a single Node of the Application under test.
pub fn start_node(name: &str) {
    RUNTIME.write().unwrap().termination_pending = false;
    debug!("{{{}}}: start per-Node thread", name);
    let node_name = name.to_string();
    let main_handle = spawn(|| unsafe {
        set_node_name(node_name);
        oak_main()
    });
    RUNTIME.write().unwrap().started(name, main_handle)
}

/// Stop the running Application under test.
pub fn stop() -> OakStatus {
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
        if overall_result == OakStatus::OK {
            overall_result = result;
        }
    }
    reset();
    overall_result
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
    let channel_idx = RUNTIME.write().unwrap().new_channel();
    msg.channels
        .push(ChannelHalf::new(Direction::Write, channel_idx));

    // Send the message (with attached write handle) into the Node under test.
    let grpc_idx = RUNTIME
        .read()
        .unwrap()
        .grpc_channel_idx
        .expect("no gRPC channel setup");
    RUNTIME
        .write()
        .unwrap()
        .channel_write_internal(grpc_idx, msg);

    // Read the serialized, encapsulated response.
    loop {
        let mut size = 0u32;
        let mut count = 0u32;
        let result = RUNTIME.write().unwrap().channel_read_internal(
            channel_idx,
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
