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

use log::{debug, error, info, warn};

use oak_abi::{ChannelReadStatus, Handle, OakStatus};
use proto::manager::NodeConfiguration_oneof_config_type;
use protobuf::ProtobufEnum;
use rand::Rng;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::{Arc, RwLock};

pub mod proto;

pub struct OakMessage {
    pub data: Vec<u8>,
    pub channels: Vec<ChannelHalf>,
}

#[derive(PartialEq, Copy, Clone, Debug, Eq, Hash)]
enum Direction {
    Read,
    Write,
}

/// Unidirectional message-based channel object that also allows fault
/// injection.
pub struct MockChannel {
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
    pub fn write_message(&mut self, msg: OakMessage) -> u32 {
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
    pub fn read_message(
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
                    Err(OakStatus::ERR_CHANNEL_EMPTY.value() as u32)
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
pub struct ChannelHalf {
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
    pub fn read_message(
        &mut self,
        size: usize,
        actual_size: &mut u32,
        handle_count: u32,
        actual_handle_count: &mut u32,
    ) -> Result<OakMessage, u32> {
        if self.direction != Direction::Read {
            return Err(OakStatus::ERR_BAD_HANDLE.value() as u32);
        }
        self.channel
            .write()
            .expect("corrupt channel ref")
            .read_message(size, actual_size, handle_count, actual_handle_count)
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

pub struct OakRuntime {
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
    halves: HashMap<Handle, ChannelHalf>,
    // Handle for a thread running the main loop for this node.
    thread_handle: Option<std::thread::JoinHandle<Result<(), oak::OakStatus>>>,
}

// Encapsulate the information needed to start a new per-Node thread.
pub struct NodeStartInfo {
    pub entrypoint: NodeMain,
    pub node_name: String,
    pub handle: Handle,
}

impl OakRuntime {
    pub fn new(node_name: Option<&str>) -> OakRuntime {
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

    pub fn termination_pending(&self) -> bool {
        self.termination_pending
    }
    pub fn set_termination_pending(&mut self, value: bool) {
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
    pub fn configure(
        &mut self,
        config: proto::manager::ApplicationConfiguration,
        entrypoints: HashMap<String, NodeMain>,
    ) -> Option<(String, NodeMain, Handle)> {
        self.set_termination_pending(false);
        self.nodes.clear();
        self.entrypoints = entrypoints;
        for node_config in config.get_node_configs() {
            match &node_config.config_type {
                None => {
                    error!("Node config {} with no type", node_config.name);
                    return None;
                }
                Some(NodeConfiguration_oneof_config_type::log_config(_)) => {
                    self.entrypoints
                        .insert(node_config.name.clone(), log_node_main);
                }
                Some(NodeConfiguration_oneof_config_type::wasm_config(_)) => {
                    // Check that we have an entrypoint corresponding to this.
                    if !self.entrypoints.contains_key(&node_config.name) {
                        error!(
                            "no entrypoint provided for Node config {}",
                            node_config.name
                        );
                        return None;
                    }
                }
                Some(NodeConfiguration_oneof_config_type::storage_config(_storage_config)) => {
                    // TODO: Implement a storage pseudo-Node
                    warn!("Storage pseudo-Node not yet implemented!");
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
        let (write_half, read_half) = self.new_channel();
        self.grpc_in_half = Some(write_half);
        let handle = node.add_half(read_half);
        self.nodes.insert(node_name.clone(), node);

        Some((node_name, entrypoint, handle))
    }
    // Record that a Node of the given name has been started in a distinct thread.
    pub fn node_started(
        &mut self,
        node_name: &str,
        join_handle: std::thread::JoinHandle<Result<(), oak::OakStatus>>,
    ) {
        self.nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name))
            .thread_handle
            .replace(join_handle);
    }
    pub fn stop_next(
        &mut self,
    ) -> Option<(String, std::thread::JoinHandle<Result<(), oak::OakStatus>>)> {
        for (name, node) in &mut self.nodes {
            if let Some(h) = node.thread_handle.take() {
                return Some((name.to_string(), h));
            }
        }
        None
    }
    pub fn reset(&mut self) {
        for node in self.nodes.values_mut() {
            node.halves.clear();
        }
        self.grpc_in_half = None;
    }
    pub fn new_channel(&mut self) -> (ChannelHalf, ChannelHalf) {
        let channel = Arc::new(RwLock::new(MockChannel::new()));
        (
            ChannelHalf::new(Direction::Write, channel.clone()),
            ChannelHalf::new(Direction::Read, channel),
        )
    }
    pub fn node_half_for_handle(&self, node_name: &str, handle: Handle) -> Option<ChannelHalf> {
        let node = self.nodes.get(node_name)?;
        let half = node.halves.get(&handle)?;
        Some(half.clone())
    }
    fn node_half_for_handle_dir(
        &self,
        node_name: &str,
        handle: Handle,
        dir: Direction,
    ) -> Option<ChannelHalf> {
        let half = self.node_half_for_handle(node_name, handle)?;
        if half.direction != dir {
            return None;
        }
        Some(half)
    }
    pub fn node_add_half(&mut self, node_name: &str, half: ChannelHalf) -> Handle {
        self.nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name))
            .add_half(half)
    }
    pub fn node_channel_create(&mut self, node_name: &str) -> (Handle, Handle) {
        let (write_half, read_half) = self.new_channel();
        let node = self
            .nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        (node.add_half(write_half), node.add_half(read_half))
    }
    pub fn node_channel_close(&mut self, node_name: &str, handle: Handle) -> u32 {
        let node = self
            .nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        node.close_channel(handle)
    }
    pub fn node_channel_write(&mut self, node_name: &str, handle: Handle, msg: OakMessage) -> u32 {
        match self.node_half_for_handle_dir(node_name, handle, Direction::Write) {
            None => OakStatus::ERR_BAD_HANDLE.value() as u32,
            Some(half) => half
                .channel
                .write()
                .expect("corrupt channel ref")
                .write_message(msg),
        }
    }
    pub fn node_channel_read(
        &mut self,
        node_name: &str,
        handle: Handle,
        size: usize,
        actual_size: &mut u32,
        handle_count: u32,
        actual_handle_count: &mut u32,
    ) -> Result<OakMessage, u32> {
        match self.node_half_for_handle_dir(node_name, handle, Direction::Read) {
            None => Err(OakStatus::ERR_BAD_HANDLE.value() as u32),
            Some(half) => half
                .channel
                .write()
                .expect("corrupt channel ref")
                .read_message(size, actual_size, handle_count, actual_handle_count),
        }
    }
    pub fn node_channel_status(&self, node_name: &str, handle: Handle) -> ChannelReadStatus {
        match self.node_half_for_handle_dir(node_name, handle, Direction::Read) {
            None => ChannelReadStatus::INVALID_CHANNEL,
            Some(half) => {
                let channel = half.channel.read().expect("corrupt channel ref");
                if !channel.messages.is_empty() {
                    ChannelReadStatus::READ_READY
                } else if channel.half_count[&Direction::Write] == 0 {
                    ChannelReadStatus::ORPHANED
                } else {
                    ChannelReadStatus::NOT_READY
                }
            }
        }
    }
    pub fn grpc_channel_setup(&mut self, node_name: &str) -> Handle {
        let (write_half, read_half) = self.new_channel();
        let node = self
            .nodes
            .get_mut(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        let read_handle = node.add_half(read_half);
        debug!(
            "set up gRPC channel to node {} with handle {}",
            node_name, read_handle
        );
        // Remember the write half of the channel to allow future test
        // injection of gRPC requests.
        self.grpc_in_half = Some(write_half);
        read_handle
    }
    pub fn grpc_channel(&self) -> Option<ChannelRef> {
        let half = self.grpc_in_half.as_ref()?;
        Some(half.channel.clone())
    }
    pub fn node_create(
        &mut self,
        node_name: String,
        config: &str,
        handle: Handle,
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
    // Internal helper to return a copy of the (data part of the) first message
    // available for reading.
    pub fn node_peek_message(&self, node_name: &str, handle: Handle) -> Option<Vec<u8>> {
        let node = self
            .nodes
            .get(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        let half = node
            .halves
            .get(&handle)
            .expect("invalid handle passed to internal helper");
        match half
            .channel
            .read()
            .expect("corrupt channel ref")
            .messages
            .front()
        {
            Some(msg) => Some(msg.data.clone()),
            None => None,
        }
    }
    // Internal helper to set the (test-only) read status for a channel.
    pub fn node_set_read_status(&mut self, node_name: &str, handle: Handle, status: Option<u32>) {
        let node = self
            .nodes
            .get(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        let half = node
            .halves
            .get(&handle)
            .expect("invalid handle passed to internal helper");
        half.channel
            .write()
            .expect("corrupt channel ref")
            .read_status = status;
    }
    // Internal helper to set the (test-only) write status for a channel.
    pub fn node_set_write_status(&mut self, node_name: &str, handle: Handle, status: Option<u32>) {
        let node = self
            .nodes
            .get(node_name)
            .unwrap_or_else(|| panic!("node {{{}}} not found", node_name));
        let half = node
            .halves
            .get(&handle)
            .expect("invalid handle passed to internal helper");
        half.channel
            .write()
            .expect("corrupt channel ref")
            .write_status = status;
    }
}

impl OakNode {
    fn new() -> OakNode {
        OakNode {
            halves: HashMap::new(),
            thread_handle: None,
        }
    }
    fn next_handle(&self) -> Handle {
        let mut rng = rand::thread_rng();
        loop {
            // Keep picking random Handle values until we find an unused (and valid) value.
            let handle = rng.gen::<Handle>();
            if handle == oak_abi::INVALID_HANDLE {
                continue;
            }
            if !self.halves.contains_key(&handle) {
                return handle;
            }
        }
    }
    fn add_half(&mut self, half: ChannelHalf) -> Handle {
        let handle = self.next_handle();
        self.halves.insert(handle, half);
        handle
    }
    fn close_channel(&mut self, handle: Handle) -> u32 {
        if !self.halves.contains_key(&handle) {
            return OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        self.halves.remove(&handle);
        OakStatus::OK.value() as u32
    }
}

/// Expected type for the main entrypoint to a Node under test.
pub type NodeMain = fn(Handle) -> Result<(), oak::OakStatus>;

// Main loop function for a log pseudo-Node.
fn log_node_main(handle: Handle) -> Result<(), oak::OakStatus> {
    if handle == oak_abi::INVALID_HANDLE {
        return Err(OakStatus::ERR_BAD_HANDLE);
    }
    let half = oak::ReadHandle {
        handle: oak::Handle::from_raw(handle),
    };
    loop {
        oak::wait_on_channels(&[half])?;
        let mut buf = Vec::<u8>::with_capacity(1024);
        let mut handles = Vec::with_capacity(8);
        oak::channel_read(half, &mut buf, &mut handles).expect("could not read from channel");
        let message = String::from_utf8_lossy(&buf);
        info!("LOG: {}", message);
    }
}
