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

use std::collections::HashMap;
use std::collections::HashSet;
use std::string::String;
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

use core::sync::atomic::Ordering::SeqCst;
use core::sync::atomic::{AtomicBool, AtomicU64};

use oak_abi::{label::Label, ChannelReadStatus, OakStatus};

use log::{debug, error};

use crate::message::Message;
use crate::node;
use crate::pretty_name_for_thread;

mod channel;
pub use channel::{Handle, HandleDirection};

struct NodeInfo {
    /// The Label associated with this node.
    ///
    /// This is set at node creation time and does not change after that.
    ///
    /// See https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels
    label: Label,

    /// A [`HashSet`] containing all the handles associated with this Node.
    // TODO(#777): this overlaps ChannelMapping.{reader,writer}
    handles: HashSet<Handle>,
}

/// An identifier for a [`Node`] that is opaque for type safety.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct NodeId(u64);

/// A node identifier reserved for the runtime that allows access to all handles and channels.
const RUNTIME_NODE_ID: NodeId = NodeId(0);
/// For testing use the same reserved identifier to allow manipulation of all handles and channels.
#[cfg(any(feature = "test_build", test))]
pub const TEST_NODE_ID: NodeId = NodeId(0);

pub struct Configuration {
    pub nodes: HashMap<String, node::Configuration>,
    pub entry_module: String,
    pub entrypoint: String,
}

/// A helper type to determine if `try_read_message` was called with not enough `bytes_capacity`
/// and/or `handles_capacity`.
pub enum ReadStatus {
    Success(Message),
    NeedsCapacity(usize, usize),
}

/// Runtime structure for configuring and running a set of Oak nodes.
pub struct Runtime {
    configuration: Configuration,
    terminating: AtomicBool,

    channels: channel::ChannelMapping,

    /// Runtime-specific state for each node instance.
    node_infos: RwLock<HashMap<NodeId, NodeInfo>>,

    /// Currently running node instances, so that [`Runtime::stop`] can terminate all of them.
    node_instances: Mutex<HashMap<NodeId, Box<dyn crate::node::Node>>>,
    next_node_id: AtomicU64,
}

impl Runtime {
    /// Creates a [`Runtime`] instance but does not start executing any node.
    pub fn create(configuration: Configuration) -> Self {
        Self {
            configuration,
            terminating: AtomicBool::new(false),
            channels: channel::ChannelMapping::new(),

            node_infos: RwLock::new(HashMap::new()),
            node_instances: Mutex::new(HashMap::new()),

            // NodeId(0) reserved for RUNTIME_NODE_ID.
            next_node_id: AtomicU64::new(1),
        }
    }

    /// Configures and runs the protobuf specified Application [`Configuration`].
    ///
    /// After starting a [`Runtime`], calling [`Runtime::stop`] will send termination signals to
    /// nodes and wait for them to terminate.
    ///
    /// Returns a writeable [`Handle`] to send messages into the [`Runtime`]. To receive messages,
    /// creating a new channel and passing the write [`Handle`] into the runtime will enable
    /// messages to be read back out.
    pub fn run(self: Arc<Self>) -> Result<Handle, OakStatus> {
        let module_name = self.configuration.entry_module.clone();
        let entrypoint = self.configuration.entrypoint.clone();

        // When first starting, we assign the least privileged label to the channel connecting the
        // outside world to the entry point node.
        let (chan_writer, chan_reader) =
            self.new_channel(RUNTIME_NODE_ID, &Label::public_trusted());

        self.clone().node_create(
            RUNTIME_NODE_ID,
            &module_name,
            &entrypoint,
            // When first starting, we assign the least privileged label to the entry point node.
            &Label::public_trusted(),
            chan_reader,
            chan_writer,
        )?;

        // We call `expect` here because this should never fail, since the channel was just created
        // and guaranteed not to have already been closed.
        self.channel_close(RUNTIME_NODE_ID, chan_reader)
            .expect("could not close channel");

        Ok(chan_writer)
    }

    /// Thread safe method for determining if the [`Runtime`] is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Thread safe method for signaling termination to a [`Runtime`] and waiting for its node
    /// threads to terminate.
    pub fn stop(&self) {
        // Set the terminating flag; this will prevent additional nodes from starting to wait again,
        // because `wait_on_channels` will return immediately with `OakStatus::ErrTerminated`.
        self.terminating.store(true, SeqCst);

        // Unpark any threads that are blocked waiting on any channels.
        for channel in self
            .channels
            .channels
            .read()
            .expect("could not acquire channel mapping")
            .values()
        {
            for thread in channel
                .waiting_threads
                .lock()
                .expect("could not acquire waiting threads for channel")
                .values()
            {
                if let Some(thread) = thread.upgrade() {
                    thread.unpark();
                }
            }
        }

        // Wait for the main thread of each node to finish. Any thread that was blocked on
        // `wait_on_channels` is now unblocked and received `OakStatus::ErrTerminated`, so we wait
        // for any additional work to be finished here. This may take an arbitrary amount of time,
        // depending on the work that the node thread has to perform, but at least we know that the
        // it will not be able to enter again in a blocking state.
        for instance in self
            .node_instances
            .lock()
            .expect("could not acquire lock on node_instances")
            .values_mut()
        {
            instance.stop();
        }
    }

    /// Allow the corresponding [`Node`] to use the [`Handle`]s passed via the iterator.
    /// This is achieved by adding the [`Handle`]s to the [`Node`]s [`HashMap`] of [`Handle`]s.
    fn track_handles_in_node<I>(&self, node_id: NodeId, handles: I)
    where
        I: IntoIterator<Item = Handle>,
    {
        if node_id == RUNTIME_NODE_ID {
            return;
        }

        let mut node_infos = self.node_infos.write().unwrap();
        let node_info = node_infos
            .get_mut(&node_id)
            .expect("Invalid node_id passed into track_handles_in_node!");

        for handle in handles {
            node_info.handles.insert(handle);
        }
    }

    /// Validate the [`NodeId`] has access to [`Handle`], returning `Err(OakStatus::ErrBadHandle)`
    /// if access is not allowed.
    fn validate_handle_access(&self, node_id: NodeId, handle: Handle) -> Result<(), OakStatus> {
        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let node_infos = self.node_infos.read().unwrap();
        // Lookup the node_id in the runtime's nodes hashmap.
        let node_info = node_infos
            .get(&node_id)
            .expect("Invalid node_id passed into validate_handle_access!");

        // Check the handle exists in the handles associated with a node, otherwise
        // return ErrBadHandle.
        if node_info.handles.contains(&handle) {
            Ok(())
        } else {
            error!(
                "validate_handle_access: handle {:?} not found in node {:?}",
                handle, node_id
            );
            Err(OakStatus::ErrBadHandle)
        }
    }

    /// Validate the [`NodeId`] has access to all [`Handle`]'s passed in the iterator, returning
    /// `Err(OakStatus::ErrBadHandle)` if access is not allowed.
    fn validate_handles_access<I>(&self, node_id: NodeId, handles: I) -> Result<(), OakStatus>
    where
        I: IntoIterator<Item = Handle>,
    {
        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let node_infos = self.node_infos.read().unwrap();
        let node_info = node_infos
            .get(&node_id)
            .expect("Invalid node_id passed into filter_optional_handles!");

        for handle in handles {
            // Check handle is accessible by the node.
            if !node_info.handles.contains(&handle) {
                error!(
                    "filter_optional_handles: handle {:?} not found in node {:?}",
                    handle, node_id
                );
                return Err(OakStatus::ErrBadHandle);
            }
        }
        Ok(())
    }

    /// Returns a clone of the [`Label`] associated with the provided `node_id`, in order to limit
    /// the scope of holding the lock on [`Runtime::node_infos`].
    ///
    /// Panics if `node_id` is invalid.
    fn get_node_label(&self, node_id: NodeId) -> Label {
        let node_infos = self
            .node_infos
            .read()
            .expect("could not acquire lock on node_infos");
        let node_info = node_infos.get(&node_id).expect("invalid node_id");
        node_info.label.clone()
    }

    /// Returns a clone of the [`Label`] associated with the provided reader `channel_handle`, in
    /// order to limit the scope of holding the lock on [`ChannelMapping::channels`].
    ///
    /// Returns an error if `channel_handle` is invalid.
    fn get_reader_channel_label(&self, channel_handle: Handle) -> Result<Label, OakStatus> {
        self.channels.with_channel(
            self.channels.get_reader_channel(channel_handle)?,
            |channel| Ok(channel.label.clone()),
        )
    }

    /// Returns a clone of the [`Label`] associated with the provided writer `channel_handle`, in
    /// order to limit the scope of holding the lock on [`ChannelMapping::channels`].
    ///
    /// Returns an error if `channel_handle` is invalid.
    fn get_writer_channel_label(&self, channel_handle: Handle) -> Result<Label, OakStatus> {
        self.channels.with_channel(
            self.channels.get_writer_channel(channel_handle)?,
            |channel| Ok(channel.label.clone()),
        )
    }

    /// Returns whether the calling node is allowed to read from the provided channel, according to
    /// their respective [`Label`]s.
    fn validate_can_read_from_channel(
        &self,
        node_id: NodeId,
        channel_handle: Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "validating whether node {:?} can read from channel {:?}",
            node_id, channel_handle
        );

        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let node_label = self.get_node_label(node_id);
        let channel_label = self.get_reader_channel_label(channel_handle)?;
        if channel_label.flows_to(&node_label) {
            debug!(
                "node {:?} can read from channel {:?}",
                node_id, channel_handle
            );
            Ok(())
        } else {
            debug!(
                "node {:?} cannot read from channel {:?}",
                node_id, channel_handle
            );
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Returns whether the calling node is allowed to read from all the provided channels,
    /// according to their respective [`Label`]s.
    fn validate_can_read_from_channels<I>(
        &self,
        node_id: NodeId,
        channel_handles: I,
    ) -> Result<(), OakStatus>
    where
        I: IntoIterator<Item = Handle>,
    {
        let all_channel_handles_ok = channel_handles.into_iter().all(|channel_handle| {
            self.validate_can_read_from_channel(node_id, channel_handle)
                .is_ok()
        });
        if all_channel_handles_ok {
            Ok(())
        } else {
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Returns whether the calling node is allowed to write to the provided channel, according to
    /// their respective [`Label`]s.
    fn validate_can_write_to_channel(
        &self,
        node_id: NodeId,
        channel_handle: Handle,
    ) -> Result<(), OakStatus> {
        debug!(
            "validating whether node {:?} can write to channel {:?}",
            node_id, channel_handle
        );

        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let node_label = self.get_node_label(node_id);
        debug!("node label: {:?}", node_label);
        let channel_label = self.get_writer_channel_label(channel_handle)?;
        debug!("channel label: {:?}", node_label);
        if node_label.flows_to(&channel_label) {
            debug!(
                "node {:?} can write to channel {:?}",
                node_id, channel_handle
            );
            Ok(())
        } else {
            debug!(
                "node {:?} cannot write to channel {:?}",
                node_id, channel_handle
            );
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Creates a new [`Channel`] and returns a `(writer handle, reader handle)` pair.
    pub fn new_channel(&self, node_id: NodeId, label: &Label) -> (Handle, Handle) {
        // TODO(#630): Check whether the calling node can create a node with the specified label.
        let (writer, reader) = self.channels.new_channel(label);
        self.track_handles_in_node(node_id, vec![writer, reader]);
        (writer, reader)
    }

    /// Reads the statuses from a slice of `Option<&ChannelReader>`s.
    /// [`ChannelReadStatus::InvalidChannel`] is set for `None` readers in the slice. For `Some(_)`
    /// readers, the result is set from a call to `has_message`.
    fn readers_statuses(
        &self,
        node_id: NodeId,
        readers: &[Option<Handle>],
    ) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|chan| {
                chan.map_or(ChannelReadStatus::InvalidChannel, |chan| {
                    self.channel_status(node_id, chan)
                        .unwrap_or(ChannelReadStatus::InvalidChannel)
                })
            })
            .collect()
    }

    /// Waits on a slice of `Option<&ChannelReader>`s, blocking until one of the following
    /// conditions:
    /// - If the [`Runtime`] is terminating this will return immediately with an `ErrTerminated`
    ///   status for each channel.
    /// - If all readers are in an erroneous status, e.g. when all [`ChannelReader`]s are orphaned,
    ///   this will immediately return the channels statuses.
    /// - If any of the channels is able to read a message, the corresponding element in the
    ///   returned vector will be set to `Ok(ReadReady)`, with `Ok(NotReady)` signaling the channel
    ///   has no message available
    ///
    /// In particular, if there is at least one channel in good status and no messages on said
    /// channel available, [`Runtime::wait_on_channels`] will continue to block until a message is
    /// available.
    pub fn wait_on_channels(
        &self,
        node_id: NodeId,
        readers: &[Option<Handle>],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        self.validate_handles_access(node_id, readers.iter().filter_map(|x| *x))?;
        self.validate_can_read_from_channels(node_id, readers.iter().filter_map(|x| *x))?;

        let thread = thread::current();
        while !self.is_terminating() {
            // Create a new Arc each iteration to be dropped after `thread::park` e.g. when the
            // thread is resumed. When the Arc is deallocated, any remaining `Weak`
            // references in `Channel`s will be orphaned. This means thread::unpark will
            // not be called multiple times. Even if thread unpark is called spuriously
            // and we wake up early, no channel statuses will be ready and so we can
            // just continue.
            //
            // Note we read statuses directly after adding waiters, before blocking to ensure that
            // there are no messages, after we have been added as a waiter.

            let thread_id = thread.id();
            let thread_ref = Arc::new(thread.clone());

            for reader in readers {
                if let Some(reader) = reader {
                    self.channels.with_channel(
                        self.channels.get_reader_channel(*reader)?,
                        |channel| {
                            channel.add_waiter(thread_id, &thread_ref);
                            Ok(())
                        },
                    )?;
                }
            }
            let statuses = self.readers_statuses(node_id, &readers);

            let all_unreadable = statuses.iter().all(|&s| {
                s == ChannelReadStatus::InvalidChannel || s == ChannelReadStatus::Orphaned
            });
            let any_ready = statuses.iter().any(|&s| s == ChannelReadStatus::ReadReady);

            if all_unreadable || any_ready {
                return Ok(statuses);
            }

            debug!(
                "wait_on_channels: channels not ready, parking thread {}",
                pretty_name_for_thread(&thread::current())
            );

            thread::park();

            debug!(
                "wait_on_channels: thread {} re-woken",
                pretty_name_for_thread(&thread::current())
            );
        }
        Err(OakStatus::ErrTerminated)
    }

    /// Write a message to a channel. Fails with [`OakStatus::ErrChannelClosed`] if the underlying
    /// channel has been orphaned.
    pub fn channel_write(
        &self,
        node_id: NodeId,
        reference: Handle,
        msg: Message,
    ) -> Result<(), OakStatus> {
        self.validate_handle_access(node_id, reference)?;
        self.validate_can_write_to_channel(node_id, reference)?;
        self.channels.with_channel(self.channels.get_writer_channel(reference)?, |channel|{

        if channel.is_orphan() {
            return Err(OakStatus::ErrChannelClosed);
        }

        let mut new_references = Vec::with_capacity(msg.channels.len());
        let mut failure = None;

        for reference in msg.channels.iter() {
            match self.channels.duplicate_reference(*reference) {
                Err(e) => {
                    failure = Some(e);
                    break;
                }
                Ok(reference) => new_references.push(reference),
            }
        }

        if let Some(err) = failure {
            for reference in new_references {
                self.channels.remove_reference(reference).expect("channel_write: Failed to deallocate channel references during backtracking from error during channel reference copying");
            }
            return Err(err);
        }

        let msg = Message { channels: new_references, ..msg };
        channel.messages.write().unwrap().push_back(msg);

        // Unpark (wake up) all waiting threads that still have live references. The first thread
        // woken can immediately read the message, and others might find `messages` is empty before
        // they are even woken. This should not be an issue (being woken does not guarantee a
        // message is available), but it could potentially result in some particular thread always
        // getting first chance to read the message.
        //
        // If a thread is woken and finds no message it will take the `waiting_threads` lock and
        // add itself again. Note that since that lock is currently held, the woken thread will add
        // itself to waiting_threads *after* we call clear below as we release the lock implicilty
        // on leaving this function.
        let mut waiting_threads = channel.waiting_threads.lock().unwrap();
        for thread in waiting_threads.values() {
            if let Some(thread) = thread.upgrade() {
                thread.unpark();
            }
        }
        waiting_threads.clear();

        Ok(())
        })
    }

    /// Thread safe. Read a message from a channel. Fails with [`OakStatus::ErrChannelClosed`] if
    /// the underlying channel is empty and has been orphaned.
    pub fn channel_read(
        &self,
        node_id: NodeId,
        reference: Handle,
    ) -> Result<Option<Message>, OakStatus> {
        self.validate_handle_access(node_id, reference)?;
        self.validate_can_read_from_channel(node_id, reference)?;
        self.channels
            .with_channel(
                self.channels.get_reader_channel(reference)?,
                |channel| match channel.messages.write().unwrap().pop_front() {
                    Some(m) => {
                        self.track_handles_in_node(node_id, vec![reference]);
                        Ok(Some(m))
                    }
                    None => {
                        if channel.is_orphan() {
                            Err(OakStatus::ErrChannelClosed)
                        } else {
                            Ok(None)
                        }
                    }
                },
            )
    }

    /// Thread safe. This function returns:
    /// - [`ChannelReadStatus::ReadReady`] if there is at least one message in the channel.
    /// - [`ChannelReadStatus::Orphaned`] if there are no messages and there are no writers
    /// - [`ChannelReadStatus::NotReady`] if there are no messages but there are some writers
    pub fn channel_status(
        &self,
        node_id: NodeId,
        reference: Handle,
    ) -> Result<ChannelReadStatus, OakStatus> {
        self.validate_handle_access(node_id, reference)?;
        self.validate_can_read_from_channel(node_id, reference)?;
        self.channels
            .with_channel(self.channels.get_reader_channel(reference)?, |channel| {
                Ok(if channel.messages.read().unwrap().front().is_some() {
                    ChannelReadStatus::ReadReady
                } else if channel.is_orphan() {
                    ChannelReadStatus::Orphaned
                } else {
                    ChannelReadStatus::NotReady
                })
            })
    }

    /// Thread safe. Reads a message from the channel if `bytes_capacity` and `handles_capacity` are
    /// large enough to accept the message. Fails with `OakStatus::ErrChannelClosed` if the
    /// underlying channel has been orphaned _and_ is empty. If there was not enough
    /// `bytes_capacity` or `handles_capacity`, `try_read_message` returns
    /// `Some(ReadStatus::NeedsCapacity(needed_bytes_capacity,needed_handles_capacity))`. Does not
    /// guarantee that the next call will succeed after capacity adjustments as another thread may
    /// have read the original message.
    pub fn channel_try_read_message(
        &self,
        node_id: NodeId,
        reference: Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<ReadStatus>, OakStatus> {
        self.validate_handle_access(node_id, reference)?;
        self.validate_can_read_from_channel(node_id, reference)?;
        let result = self.channels
            .with_channel(self.channels.get_reader_channel(reference)?, |channel| {
                let mut messages = channel.messages.write().unwrap();
                match messages.front() {
                    Some(front) => {
                        let req_bytes_capacity = front.data.len();
                        let req_handles_capacity = front.channels.len();

                        Ok(Some(
                            if req_bytes_capacity > bytes_capacity
                                || req_handles_capacity > handles_capacity
                            {
                                ReadStatus::NeedsCapacity(req_bytes_capacity, req_handles_capacity)
                            } else {
                                let msg = messages.pop_front().expect( "Front element disappeared while we were holding the write lock!");
                                ReadStatus::Success(msg)
                            },
                        ))
                    }
                    None => {
                        if channel.is_orphan() {
                            Err(OakStatus::ErrChannelClosed)
                        } else {
                            Ok(None)
                        }
                    }
                }
            });

        // Add handles outside the channels lock so we don't hold the node lock inside the channel
        // lock.
        if let Ok(Some(ReadStatus::Success(ref msg))) = result {
            self.track_handles_in_node(node_id, msg.channels.clone());
        }

        result
    }

    /// Return the direction of a [`Handle`]. This is useful when reading
    /// [`Messages`] which contain [`Handle`]'s.
    pub fn channel_get_direction(
        &self,
        node_id: NodeId,
        reference: Handle,
    ) -> Result<HandleDirection, OakStatus> {
        self.validate_handle_access(node_id, reference)?;
        // TODO(#630): Check whether the calling node can read from the specified handle. Currently,
        // performing this check seems to get tests to hang forever.
        {
            if self
                .channels
                .readers
                .read()
                .unwrap()
                .contains_key(&reference)
            {
                return Ok(HandleDirection::Read);
            }
        }
        {
            if self
                .channels
                .writers
                .read()
                .unwrap()
                .contains_key(&reference)
            {
                return Ok(HandleDirection::Write);
            }
        }
        Err(OakStatus::ErrBadHandle)
    }

    /// Close a [`Handle`], potentially orphaning the underlying [`channel::Channel`].
    pub fn channel_close(&self, node_id: NodeId, reference: Handle) -> Result<(), OakStatus> {
        self.validate_handle_access(node_id, reference)?;

        if node_id != RUNTIME_NODE_ID {
            // Remove handle from the nodes available handles
            let mut node_infos = self.node_infos.write().unwrap();
            let node_info = node_infos
                .get_mut(&node_id)
                .expect("channel_close: No such node_id");
            node_info.handles.remove(&reference);
        }

        self.channels.remove_reference(reference)
    }

    /// Create a fresh [`NodeId`].
    fn new_node_reference(&self) -> NodeId {
        NodeId(self.next_node_id.fetch_add(1, SeqCst))
    }

    /// Remove a [`Node`] by [`NodeId`] from the [`Runtime`].
    pub fn remove_node_id(&self, node_id: NodeId) {
        {
            // Do not remove the node if it is RUNTIME_NODE_ID
            if node_id == RUNTIME_NODE_ID {
                return;
            }

            // Close any remaining handles
            let remaining_handles: Vec<_> = {
                let node_infos = self.node_infos.read().unwrap();
                let node_info = node_infos
                    .get(&node_id)
                    .expect("remove_node_id: No such node_id");
                node_info.handles.iter().copied().collect()
            };

            debug!(
                "remove_node_id: node_id {:?} had open channels on exit: {:?}",
                node_id, remaining_handles
            );

            for handle in remaining_handles {
                self.channel_close(node_id, handle)
                    .expect("remove_node_id: Unable to close hanging channel!");
            }
        }

        self.node_infos
            .write()
            .unwrap()
            .remove(&node_id)
            .expect("remove_node_id: Node didn't exist!");
    }

    /// Add an [`NodeId`] [`NodeInfo`] pair to the [`Runtime`]. This method temporarily holds the
    /// [`Runtime::node_infos`] write lock.
    fn add_node_info(&self, reference: NodeId, node_info: NodeInfo) {
        self.node_infos
            .write()
            .expect("could not acquire lock on node_infos")
            .insert(reference, node_info);
    }

    /// Add an [`NodeId`] [`crate::node::Node`] pair to the [`Runtime`]. This method temporarily
    /// holds the [`Runtime::node_instances`] lock.
    fn add_node_instance(&self, node_reference: NodeId, node_instance: Box<dyn crate::node::Node>) {
        self.node_instances
            .lock()
            .expect("could not acquire lock on node_instances")
            .insert(node_reference, node_instance);
    }

    /// Thread safe method that attempts to create a node within the [`Runtime`] corresponding to a
    /// given module name and entrypoint. The `reader: ChannelReader` is passed to the newly
    /// created node.
    ///
    /// The caller also specifies a [`Label`], which is assigned to the newly created node. See
    /// <https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels> for more
    /// information on labels.
    ///
    /// This method is defined on [`Arc`] and not [`Runtime`] itself, so that the [`Arc`] can clone
    /// itself and be passed to [`crate::node::Configuration::new_instance`] to be given to a new
    /// node thread.
    pub fn node_create(
        self: Arc<Self>,
        node_id: NodeId,
        module_name: &str,
        entrypoint: &str,
        label: &Label,
        reader: Handle,
        writer: Handle,
    ) -> Result<(), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        if node_id != RUNTIME_NODE_ID {
            let node_label = self.get_node_label(node_id);
            if !node_label.flows_to(label) {
                return Err(OakStatus::ErrPermissionDenied);
            }
        }

        let reference = self.new_node_reference();
        let runtime_proxy = RuntimeProxy {
            runtime: self.clone(),
            node_id: reference,
        };

        let reader = self.channels.duplicate_reference(reader)?;
        let writer = self.channels.duplicate_reference(writer)?;

        let instance = self
            .configuration
            .nodes
            .get(module_name)
            .ok_or(OakStatus::ErrInvalidArgs)
            .map(|conf| {
                // This only creates a node instance, but does not start it.
                conf.create_node(
                    module_name,
                    runtime_proxy,
                    entrypoint.to_owned(),
                    reader,
                    writer,
                )
            })?;

        self.node_start_instance(reference, instance, label, vec![reader])?;

        Ok(())
    }

    /// Starts a newly created node instance, by first initializing the necessary [`NodeInfo`] data
    /// structure in [`Runtime`], allowing it to access the provided [`Handle`]s, then calling
    /// [`Node::start`] on the instance, and finally storing a reference to the running instance
    /// in [`Runtime::node_instances`] so that it can later be terminated.
    fn node_start_instance<I>(
        &self,
        node_reference: NodeId,
        mut node_instance: Box<dyn crate::node::Node>,
        label: &Label,
        initial_handles: I,
    ) -> Result<(), OakStatus>
    where
        I: IntoIterator<Item = Handle>,
    {
        // First create the necessary info data structure in the Runtime, otherwise calls that the
        // node makes to the Runtime during `Node::start` (synchronously or asynchronously) may
        // fail.
        self.add_node_info(
            node_reference,
            NodeInfo {
                label: label.clone(),
                handles: HashSet::new(),
            },
        );

        // Make sure that the provided initial handles are tracked in the newly created node from
        // the start.
        self.track_handles_in_node(node_reference, initial_handles);

        // Try to start the node instance, and store the result in a temporary variable to be
        // returned later.
        //
        // In order for this to work correctly, the `NodeInfo` entry must already exist in
        // `Runtime`, which is why we could not start this instance before the call to
        // `Runtime::add_node_info` above.
        //
        // On the other hand, we also cannot start it after the call to `Runtime::add_node_instance`
        // below, because that takes ownership of the instance itself.
        //
        // We also want no locks to be held while the instance is starting.
        let result = node_instance.start();

        // Regardless of the result of `Node::start`, insert the now running instance to the list of
        // running instances (by moving it), so that `Node::stop` will be called on it eventually.
        self.add_node_instance(node_reference, node_instance);

        // Return the result of `Node::start`.
        result
    }

    pub fn new_runtime_proxy(self: Arc<Self>) -> RuntimeProxy {
        RuntimeProxy {
            runtime: self.clone(),
            node_id: self.new_node_reference(),
        }
    }
}

/// A proxy object that binds together a reference to the underlying [`Runtime`] with a single
/// [`NodeId`].
///
/// This can be considered as the interface to the [`Runtime`] that node and pseudo-node
/// implementations have access to.
///
/// Each [`RuntimeProxy`] instance is used by an individual node or pseudo-node instance to
/// communicate with the [`Runtime`]. Nodes do not have direct access to the [`Runtime`] apart from
/// through [`RuntimeProxy`], which exposes a more limited API, and ensures that nodes cannot
/// impersonate each other.
///
/// Individual methods simply forward to corresponding methods on the underlying [`Runtime`], by
/// partially applying the first argument.
#[derive(Clone)]
pub struct RuntimeProxy {
    runtime: Arc<Runtime>,
    node_id: NodeId,
}

impl RuntimeProxy {
    /// See [`Runtime::is_terminating`].
    pub fn is_terminating(&self) -> bool {
        self.runtime.is_terminating()
    }

    /// See [`Runtime::remove_node_id`].
    pub fn exit_node(&self) {
        self.runtime.remove_node_id(self.node_id)
    }

    /// See [`Runtime::node_create`].
    pub fn node_create(
        &self,
        module_name: &str,
        entrypoint: &str,
        label: &Label,
        channel_read_handle: Handle,
    ) -> Result<(), OakStatus> {
        self.runtime.clone().node_create(
            self.node_id,
            module_name,
            entrypoint,
            label,
            channel_read_handle,
        )
    }

    /// See [`Runtime::new_channel`].
    pub fn channel_create(&self, label: &Label) -> (Handle, Handle) {
        self.runtime.new_channel(self.node_id, label)
    }

    /// See [`Runtime::channel_close`].
    pub fn channel_close(&self, channel_handle: Handle) -> Result<(), OakStatus> {
        self.runtime.channel_close(self.node_id, channel_handle)
    }

    /// See [`Runtime::wait_on_channels`].
    pub fn wait_on_channels(
        &self,
        channel_read_handles: &[Option<Handle>],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        self.runtime
            .wait_on_channels(self.node_id, channel_read_handles)
    }

    /// See [`Runtime::channel_write`].
    pub fn channel_write(
        &self,
        channel_write_handle: Handle,
        msg: Message,
    ) -> Result<(), OakStatus> {
        self.runtime
            .channel_write(self.node_id, channel_write_handle, msg)
    }

    /// See [`Runtime::channel_read`].
    pub fn channel_read(&self, channel_read_handle: Handle) -> Result<Option<Message>, OakStatus> {
        self.runtime.channel_read(self.node_id, channel_read_handle)
    }

    /// See [`Runtime::channel_try_read_message`].
    pub fn channel_try_read_message(
        &self,
        channel_read_handle: Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<ReadStatus>, OakStatus> {
        self.runtime.channel_try_read_message(
            self.node_id,
            channel_read_handle,
            bytes_capacity,
            handles_capacity,
        )
    }

    /// See [`Runtime::channel_get_direction`].
    pub fn channel_get_direction(
        &self,
        channel_handle: Handle,
    ) -> Result<HandleDirection, OakStatus> {
        self.runtime
            .channel_get_direction(self.node_id, channel_handle)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type NodeBody = dyn Fn(&RuntimeProxy) -> Result<(), OakStatus> + Send + Sync;

    /// Runs the provided function as if it were the body of a [`Node`] implementation, which is
    /// instantiated by the [`Runtime`] with the provided [`Label`].
    fn run_node_body(node_label: Label, node_body: Box<NodeBody>) {
        let configuration = crate::runtime::Configuration {
            nodes: maplit::hashmap![
                "log".to_string() => crate::node::Configuration::LogNode,
            ],
            entry_module: "test_module".to_string(),
            entrypoint: "test_function".to_string(),
        };
        let runtime = Arc::new(crate::runtime::Runtime::create(configuration));

        struct TestNode {
            runtime: RuntimeProxy,
            node_body: Box<NodeBody>,
        };

        impl crate::node::Node for TestNode {
            fn start(&mut self) -> Result<(), OakStatus> {
                (self.node_body)(&self.runtime)
            }
            fn stop(&mut self) {}
        }

        // Manually allocate a new [`NodeId`].
        let node_reference = runtime.new_node_reference();
        let runtime_proxy = RuntimeProxy {
            runtime: runtime.clone(),
            node_id: node_reference,
        };

        let node_instance = TestNode {
            runtime: runtime_proxy,
            node_body,
        };

        let result = runtime.node_start_instance(
            node_reference,
            Box::new(node_instance),
            &node_label,
            vec![],
        );
        assert_eq!(Ok(()), result);
    }

    /// Create a test node that creates a channel and succeeds.
    #[test]
    fn create_channel_success() {
        run_node_body(
            Label::public_trusted(),
            Box::new(|runtime| {
                // Attempt to perform an operation that requires the [`Runtime`] to have created an
                // appropriate [`NodeInfo`] instanace.
                let (_write_handle, _read_handle) =
                    runtime.channel_create(&Label::public_trusted());
                Ok(())
            }),
        );
    }

    /// Create a test node that creates a node and succeeds.
    #[test]
    fn create_node_success() {
        run_node_body(
            Label::public_trusted(),
            Box::new(|runtime| {
                let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());
                let result = runtime.clone().node_create(
                    "log",
                    "unused",
                    &Label::public_trusted(),
                    read_handle,
                );
                assert_eq!(Ok(()), result);
                Ok(())
            }),
        );
    }

    /// Create a test node that creates a node with a non-existing configuration name and fails.
    #[test]
    fn create_node_invalid_configuration() {
        run_node_body(
            Label::public_trusted(),
            Box::new(|runtime| {
                let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());
                let result = runtime.clone().node_create(
                    "invalid-configuration-name",
                    "unused",
                    &Label::public_trusted(),
                    read_handle,
                );
                assert_eq!(Err(OakStatus::ErrInvalidArgs), result);
                Ok(())
            }),
        );
    }

    /// Create a test node that creates a node with a more public label and fails.
    ///
    /// If this succeeded, it would be a violation of information flow control, since the original
    /// secret node would be able to spawn "public" nodes and use their side effects as a covert
    /// channel to exfiltrate secret data.
    #[test]
    fn create_node_more_public_label() {
        let secret_label = Label {
            secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
                1, 1, 1,
            ])],
            integrity_tags: vec![],
        };
        run_node_body(
            secret_label,
            Box::new(|runtime| {
                let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());
                let result = runtime.clone().node_create(
                    "log",
                    "unused",
                    &Label::public_trusted(),
                    read_handle,
                );
                assert_eq!(Err(OakStatus::ErrPermissionDenied), result);
                Ok(())
            }),
        );
    }
}
