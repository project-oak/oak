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

use oak_abi::{ChannelReadStatus, OakStatus};

use log::{debug, error};

use crate::message::Message;
use crate::node;

mod channel;
pub use channel::{Handle, HandleDirection};

struct Node {
    #[allow(dead_code)]
    reference: NodeId,

    // An option type allows the instance to be swapped out during `runtime.stop`
    instance: Option<Box<dyn crate::node::Node>>,
    /// The Label associated with this node.
    ///
    /// This is set at node creation time and does not change after that.
    ///
    /// See https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels
    // TODO(#630): Remove exception when label tracking is implemented.
    #[allow(dead_code)]
    label: oak_abi::label::Label,

    /// A [`HashSet`] containing all the handles associated with this Node.
    // TODO(#777): this overlaps ChannelMapping.{reader,writer}
    handles: Mutex<HashSet<Handle>>,
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

    nodes: RwLock<HashMap<NodeId, Node>>,
    next_node_id: AtomicU64,
}

impl Runtime {
    /// Creates a [`Runtime`] instance but does not start executing any node.
    pub fn create(configuration: Configuration) -> Self {
        Self {
            configuration,
            terminating: AtomicBool::new(false),
            channels: channel::ChannelMapping::new(),
            nodes: RwLock::new(HashMap::new()),

            // NodeId(0) reserved for RUNTIME_NODE_ID.
            next_node_id: AtomicU64::new(1),
        }
    }

    /// Converts a [`Runtime`] instance into a [`RuntimeRef`].
    pub fn into_ref(self) -> RuntimeRef {
        RuntimeRef(Arc::new(self))
    }

    /// Configures and runs the protobuf specified Application [`Configuration`].
    ///
    /// After starting a [`Runtime`], calling [`Runtime::stop`] will send termination signals to
    /// nodes and wait for them to terminate.
    ///
    /// Returns a [`RuntimeRef`] reference to the created runtime, and a writeable [`Handle`] to
    /// send messages into the runtime. To receive messages, creating a new channel and passing
    /// the write [`Handle`] into the runtime will enable messages to be read back out.
    pub fn run(self) -> Result<(RuntimeRef, Handle), OakStatus> {
        let module_name = self.configuration.entry_module.clone();
        let entrypoint = self.configuration.entrypoint.clone();

        let runtime_ref = self.into_ref();

        // When first starting, we assign the least privileged label to the channel connecting the
        // outside world to the entry point node.
        let (chan_writer, chan_reader) =
            runtime_ref.new_channel(RUNTIME_NODE_ID, &oak_abi::label::Label::public_trusted());

        runtime_ref.node_create(
            RUNTIME_NODE_ID,
            &module_name,
            &entrypoint,
            // When first starting, we assign the least privileged label to the entry point node.
            &oak_abi::label::Label::public_trusted(),
            chan_reader,
        )?;

        // We call `expect` here because this should never fail, since the channel was just created
        // and guaranteed not to have already been closed.
        runtime_ref
            .channel_close(RUNTIME_NODE_ID, chan_reader)
            .expect("could not close channel");

        Ok((runtime_ref, chan_writer))
    }

    /// Thread safe method for determining if the [`Runtime`] is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Thread safe method for signaling termination to a [`Runtime`] and waiting for its node
    /// threads to terminate.
    pub fn stop(&self) {
        // Take the list of nodes out of the runtime instance, and set the terminating flag; this
        // will prevent additional nodes from starting to wait again, because `wait_on_channels`
        // will return immediately with `OakStatus::ErrTerminated`.
        let instances: Vec<_> = {
            let mut nodes = self.nodes.write().unwrap();
            self.terminating.store(true, SeqCst);

            nodes
                .values_mut()
                .filter_map(|n| n.instance.take())
                .collect()
        };

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
        for mut instance in instances {
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

        let nodes = self.nodes.read().unwrap();
        let node = nodes
            .get(&node_id)
            .expect("Invalid node_id passed into track_handles_in_node!");

        let mut tracked_handles = node.handles.lock().unwrap();
        for handle in handles {
            tracked_handles.insert(handle);
        }
    }

    /// Validate the [`NodeId`] has access to [`Handle`], returning `Err(OakStatus::ErrBadHandle)`
    /// if access is not allowed.
    fn validate_handle_access(&self, node_id: NodeId, handle: Handle) -> Result<(), OakStatus> {
        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let nodes = self.nodes.read().unwrap();
        // Lookup the node_id in the runtime's nodes hashmap.
        let node = nodes
            .get(&node_id)
            .expect("Invalid node_id passed into validate_handle_access!");
        let tracked_handles = node.handles.lock().unwrap();

        // Check the handle exists in the handles associated with a node, otherwise
        // return ErrBadHandle.
        if tracked_handles.contains(&handle) {
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
    fn validate_handles_access<'a, I>(&self, node_id: NodeId, handles: I) -> Result<(), OakStatus>
    where
        I: IntoIterator<Item = &'a Handle>,
    {
        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let nodes = self.nodes.read().unwrap();
        let node = nodes
            .get(&node_id)
            .expect("Invalid node_id passed into filter_optional_handles!");

        let tracked_handles = node.handles.lock().unwrap();
        for handle in handles {
            // Check handle is accessible by the node.
            if !tracked_handles.contains(&handle) {
                error!(
                    "filter_optional_handles: handle {:?} not found in node {:?}",
                    handle, node_id
                );
                return Err(OakStatus::ErrBadHandle);
            }
        }
        Ok(())
    }

    /// Creates a new [`Channel`] and returns a `(writer handle, reader handle)` pair.
    pub fn new_channel(&self, node_id: NodeId, label: &oak_abi::label::Label) -> (Handle, Handle) {
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
        self.validate_handles_access(node_id, readers.iter().filter_map(|x| x.as_ref()))?;

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
                "wait_on_channels: channels not ready, parking thread {:?}",
                thread::current()
            );

            thread::park();

            debug!("wait_on_channels: thread {:?} re-woken", thread::current());
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
        self.channels.with_channel(self.channels.get_writer_channel(reference)?, |channel|{

        if channel.is_orphan() {
            return Err(OakStatus::ErrChannelClosed);
        }

        {
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

            let mut messages = channel.messages.write().unwrap();

            messages.push_back(msg);
        }

        let mut waiting_threads = channel.waiting_threads.lock().unwrap();

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
        self.channels
            .with_channel(self.channels.get_reader_channel(reference)?, |channel| {
                let mut messages = channel.messages.write().unwrap();
                match messages.pop_front() {
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
                }
            })
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
        self.channels
            .with_channel(self.channels.get_reader_channel(reference)?, |channel| {
                let messages = channel.messages.read().unwrap();
                Ok(if messages.front().is_some() {
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
        {
            let readers = self.channels.readers.read().unwrap();
            if readers.contains_key(&reference) {
                return Ok(HandleDirection::Read);
            }
        }
        {
            let writers = self.channels.writers.read().unwrap();
            if writers.contains_key(&reference) {
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
            let nodes = self.nodes.read().unwrap();
            let node = nodes.get(&node_id).expect("channel_close: No such node_id");
            let mut handles = node.handles.lock().unwrap();
            handles.remove(&reference);
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
            // Close any remaining handles
            let remaining_handles: Vec<_> = {
                let nodes = self.nodes.read().unwrap();
                let node = nodes
                    .get(&node_id)
                    .expect("remove_node_id: No such node_id");
                let handles = node.handles.lock().unwrap();
                handles.iter().copied().collect()
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

        let mut nodes = self.nodes.write().unwrap();
        nodes
            .remove(&node_id)
            .expect("remove_node_id: Node didn't exist!");
    }

    /// Add an [`NodeId`] [`Node`] pair to the [`Runtime`]. This method temporarily holds the node
    /// write lock.
    fn add_running_node(&self, reference: NodeId, node: Node) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.insert(reference, node);
    }
}

/// A reference to a [`Runtime`].
#[derive(Clone)]
pub struct RuntimeRef(Arc<Runtime>);

impl RuntimeRef {
    /// Thread safe method that attempts to create a node within the [`Runtime`] corresponding to a
    /// given module name and entrypoint. The `reader: ChannelReader` is passed to the newly
    /// created node.
    ///
    /// The caller also specifies a [`oak_abi::label::Label`], which is assigned to the newly
    /// created node. See <https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels>
    /// for more information on labels.
    ///
    /// [`RuntimeRef::node_create`] is a method of [`RuntimeRef`] and not [`Runtime`], so that the
    /// underlying `Arc<Runtime>` can be passed to [`crate::node::Configuration::new_instance`]
    /// and given to a new node thread.
    pub fn node_create(
        &self,
        _node_id: NodeId,
        module_name: &str,
        entrypoint: &str,
        label: &oak_abi::label::Label,
        reader: Handle,
    ) -> Result<(), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        // TODO(#630): Check whether the label of the caller "flows to" the provided label. In order
        // to do that we first need to provide a reference to the caller node as a parameter to this
        // function.

        let reference = self.new_node_reference();

        let reader = self.channels.duplicate_reference(reader)?;

        let mut instance = self
            .configuration
            .nodes
            .get(module_name)
            .ok_or(OakStatus::ErrInvalidArgs)
            .map(|conf| {
                // This only creates a node instance, but does not start it.
                conf.create_node(
                    module_name,
                    self.clone(),
                    reference,
                    entrypoint.to_owned(),
                    reader,
                )
            })?;

        // Try starting the node instance first. If this fails, then directly return the error to
        // the caller.
        instance.start()?;

        // If the node was successfully started, insert it in the list of currently running
        // nodes.
        self.add_running_node(
            reference,
            Node {
                reference,
                instance: Some(instance),
                label: label.clone(),
                handles: Mutex::new(vec![reader].into_iter().collect()),
            },
        );

        Ok(())
    }
}

impl std::ops::Deref for RuntimeRef {
    type Target = Runtime;

    #[inline]
    fn deref(&self) -> &Runtime {
        &self.0
    }
}
