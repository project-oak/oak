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

//! Core Runtime functionality, allowing manipulation of Nodes, channels and messages.

use crate::{
    message::{Message, NodeMessage},
    metrics::Metrics,
    node,
    proto::oak::introspection_events::{event::EventDetails, NodeCreated},
    runtime::channel::{with_reader_channel, with_writer_channel, Channel},
    GrpcConfiguration,
};
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering::SeqCst};
use itertools::Itertools;
use log::{debug, error, info, trace, warn};
use oak_abi::{
    label::{Label, Tag},
    proto::oak::application::{ApplicationConfiguration, NodeConfiguration},
    ChannelReadStatus, OakStatus,
};
use prometheus::proto::MetricFamily;
use rand::RngCore;
use std::{
    collections::{HashMap, HashSet},
    string::String,
    sync::{Arc, Mutex, RwLock},
    thread,
    thread::JoinHandle,
};
use tokio::sync::oneshot;

mod channel;
#[cfg(feature = "oak_debug")]
pub mod graph;
#[cfg(feature = "oak_debug")]
mod introspect;
mod introspection_events;
mod proxy;
#[cfg(test)]
pub mod tests;

pub use channel::{ChannelHalf, ChannelHalfDirection};
pub use proxy::RuntimeProxy;

struct NodeStopper {
    node_name: String,

    /// Handle used for joining the Node thread.
    join_handle: JoinHandle<()>,

    /// A notification sender object whose receiver is sent to the Node.
    /// The agreement is that the Runtime will notify the Node upon termination
    /// and then start waiting on the join handle. It's up to the Node to figure
    /// out how to actually terminate when receiving a notification.
    notify_sender: oneshot::Sender<()>,
}

impl NodeStopper {
    /// Sends a notification to the Node and joins its thread.
    fn stop_node(self) -> thread::Result<()> {
        let node_name = &self.node_name;
        self.notify_sender
            .send(())
            // Notification errors are discarded since not all of the Nodes save
            // and use the [`oneshot::Receiver`].
            .unwrap_or_else(|()| {
                debug!("{} already dropped `notify_receiver`.", node_name);
            });
        debug!("join thread for node {}...", self.node_name);
        let result = self.join_handle.join();
        debug!("join thread for node {}...done", self.node_name);
        result
    }
}

impl std::fmt::Debug for NodeStopper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{node_name='{}', join_handle={:?}, notify_sender={:?}}}",
            self.node_name, self.join_handle, self.notify_sender,
        )
    }
}

struct NodeInfo {
    /// Name for the Node in debugging output.
    name: String,

    /// The Label associated with this Node.
    ///
    /// This is set at Node creation time and does not change after that.
    ///
    /// See https://github.com/project-oak/oak/blob/main/docs/concepts.md#labels
    label: Label,

    /// The downgrading privilege of this Node.
    privilege: NodePrivilege,

    /// Map of ABI handles to channels.
    abi_handles: HashMap<oak_abi::Handle, ChannelHalf>,

    /// If the Node is currently running, holds the [`NodeStopper`] (with one
    /// small exception, when the Runtime is in the process of closing down and
    /// the [`NodeStopper`] is held by the shutdown processing code).
    node_stopper: Option<NodeStopper>,
}

/// The downgrading (declassification + endorsement) privilege associated with a Node instance.
///
/// See https://github.com/project-oak/oak/blob/main/docs/concepts.md#downgrades
#[derive(Debug, Default, Clone)]
pub struct NodePrivilege {
    /// Tags that may be declassified (removed from the confidentiality component of a label) by
    /// the Node.
    can_declassify_confidentiality_tags: HashSet<Tag>,

    /// Tags that may be endorsed (added to the integrity component of a label) by the Node.
    can_endorse_integrity_tags: HashSet<Tag>,
}

impl NodePrivilege {
    pub fn new(
        can_declassify_confidentiality_tags: HashSet<Tag>,
        can_endorse_integrity_tags: HashSet<Tag>,
    ) -> Self {
        Self {
            can_declassify_confidentiality_tags,
            can_endorse_integrity_tags,
        }
    }
}

impl std::fmt::Debug for NodeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "NodeInfo {{'{}', label={:?}, node_stopper={:?}, handles=[",
            self.name, self.label, self.node_stopper,
        )?;
        write!(
            f,
            "{}",
            self.abi_handles
                .iter()
                .map(|(handle, half)| format!("{} => {:?}", handle, half))
                .join(", ")
        )?;
        write!(f, "]}}")
    }
}

/// A unique internal identifier for a Node or pseudo-Node instance.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, PartialOrd, Ord)]
pub struct NodeId(pub u64);

/// Helper types to indicate whether a channel read operation has succeed or has failed with not
/// enough `bytes_capacity` and/or `handles_capacity`.
#[derive(Debug)]
pub enum NodeReadStatus {
    Success(NodeMessage),
    NeedsCapacity(usize, usize),
}
pub enum ReadStatus {
    Success(Message),
    NeedsCapacity(usize, usize),
}

/// Information for managing an associated server.
pub struct AuxServer {
    pub name: String,
    pub join_handle: Option<JoinHandle<()>>,
    pub notify_sender: Option<tokio::sync::oneshot::Sender<()>>,
}

impl AuxServer {
    /// Start a new auxiliary server, running on its own thread.
    fn new<F: FnOnce(u16, Arc<Runtime>, tokio::sync::oneshot::Receiver<()>) + 'static + Send>(
        name: &str,
        port: u16,
        runtime: Arc<Runtime>,
        f: F,
    ) -> Self {
        let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();
        info!("spawning {} server on new thread", name);
        let join_handle = thread::Builder::new()
            .name(format!("{}-server", name))
            .spawn(move || f(port, runtime, notify_receiver))
            .expect("failed to spawn introspection thread");
        AuxServer {
            name: name.to_string(),
            join_handle: Some(join_handle),
            notify_sender: Some(notify_sender),
        }
    }
}

impl Drop for AuxServer {
    /// Dropping an auxiliary server involves notifying it that it should terminate,
    /// then joining its thread.
    fn drop(&mut self) {
        let join_handle = self.join_handle.take();
        let notify_sender = self.notify_sender.take();
        if let Some(notify_sender) = notify_sender {
            info!("stopping {} server", self.name);
            // The auxiliary server may already have stopped, so ignore
            // errors when sending the stop notification.
            let _ = notify_sender.send(());
        }
        if let Some(join_handle) = join_handle {
            let result = join_handle.join();
            info!("stopped {} server, result {:?}", self.name, result);
        }
    }
}

/// Runtime structure for configuring and running a set of Oak Nodes.
pub struct Runtime {
    application_configuration: ApplicationConfiguration,
    grpc_configuration: GrpcConfiguration,

    terminating: AtomicBool,

    next_channel_id: AtomicU64,

    /// Runtime-specific state for each Node instance.
    node_infos: RwLock<HashMap<NodeId, NodeInfo>>,

    next_node_id: AtomicU64,

    aux_servers: Mutex<Vec<AuxServer>>,

    pub metrics_data: Metrics,
}

/// Manual implementation of the [`Drop`] trait to ensure that all components of
/// the [`Runtime`] are stopped before the object is dropped.
impl Drop for Runtime {
    fn drop(&mut self) {
        self.stop();
        info!("Runtime instance dropped");
    }
}

// Methods which translate between ABI handles (Node-relative u64 values) and `ChannelHalf`
// values.
impl Runtime {
    /// Register a [`ChannelHalf`] with a Node, returning the new handle value for it.
    fn new_abi_handle(&self, node_id: NodeId, half: ChannelHalf) -> oak_abi::Handle {
        let mut node_infos = self.node_infos.write().unwrap();
        let node_info = node_infos.get_mut(&node_id).expect("Invalid node_id");
        loop {
            let candidate = rand::thread_rng().next_u64();
            if node_info.abi_handles.get(&candidate).is_none() {
                debug!(
                    "{:?}: new ABI handle {} maps to {:?}",
                    node_id, candidate, half
                );
                node_info.abi_handles.insert(candidate, half);
                return candidate;
            }
        }
    }
    /// Remove the handle from the Node's handle table.
    fn drop_abi_handle(&self, node_id: NodeId, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        let mut node_infos = self.node_infos.write().unwrap();
        let node_info = node_infos.get_mut(&node_id).expect("Invalid node_id");
        node_info
            .abi_handles
            .remove(&handle)
            .ok_or(OakStatus::ErrBadHandle)
            .map(|_half| ())
    }
    /// Convert an ABI handle to an internal [`ChannelHalf`].
    fn abi_to_half(
        &self,
        node_id: NodeId,
        handle: oak_abi::Handle,
    ) -> Result<ChannelHalf, OakStatus> {
        let node_infos = self.node_infos.read().unwrap();
        let node_info = node_infos.get(&node_id).expect("Invalid node_id");
        let half = node_info
            .abi_handles
            .get(&handle)
            .ok_or(OakStatus::ErrBadHandle)?;
        trace!("{:?}: map ABI handle {} to {:?}", node_id, handle, half);
        Ok(half.clone())
    }
    /// Convert an ABI handle to an internal [`ChannelHalf`], but fail
    /// the operation if the handle is not for the read half of the channel.
    fn abi_to_read_half(
        &self,
        node_id: NodeId,
        handle: oak_abi::Handle,
    ) -> Result<ChannelHalf, OakStatus> {
        let half = self.abi_to_half(node_id, handle)?;
        match half.direction {
            ChannelHalfDirection::Read => Ok(half),
            ChannelHalfDirection::Write => Err(OakStatus::ErrBadHandle),
        }
    }
    /// Convert an ABI handle to an internal [`ChannelHalf`], but fail
    /// the operation if the handle is not for the write half of the channel.
    fn abi_to_write_half(
        &self,
        node_id: NodeId,
        handle: oak_abi::Handle,
    ) -> Result<ChannelHalf, OakStatus> {
        let half = self.abi_to_half(node_id, handle)?;
        match half.direction {
            ChannelHalfDirection::Read => Err(OakStatus::ErrBadHandle),
            ChannelHalfDirection::Write => Ok(half),
        }
    }

    /// Return the direction of an ABI handle.
    pub(crate) fn abi_direction(
        &self,
        node_id: NodeId,
        handle: oak_abi::Handle,
    ) -> Result<ChannelHalfDirection, OakStatus> {
        let half = self.abi_to_half(node_id, handle)?;
        Ok(half.direction)
    }

    /// Return the accumulated metrics for the `Runtime`.
    pub fn gather_metrics(&self) -> Vec<MetricFamily> {
        self.metrics_data.gather()
    }
}

// Methods which handle exposed Runtime functionality.
impl Runtime {
    /// Return whether the [`Runtime`] is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Signal termination to a [`Runtime`] and wait for its Node threads to terminate.
    pub fn stop(&self) {
        info!("stopping runtime instance");

        // Terminate any running servers.
        self.aux_servers.lock().unwrap().drain(..);

        // Set the terminating flag; this will prevent additional Nodes from starting to wait again,
        // because `wait_on_channels` will return immediately with `OakStatus::ErrTerminated`.
        self.terminating.store(true, SeqCst);

        // Unpark any threads that are blocked waiting on any channels.
        self.notify_all_waiters();

        // Wait for the main thread of each Node to finish. Any thread that was blocked on
        // `wait_on_channels` is now unblocked and received `OakStatus::ErrTerminated`, so we wait
        // for any additional work to be finished here. This may take an arbitrary amount of time,
        // depending on the work that the Node thread has to perform, but at least we know that the
        // it will not be able to enter again in a blocking state.
        let node_stoppers = self.take_node_stoppers();
        for (node_id, node_stopper_opt) in node_stoppers {
            if let Some(node_stopper) = node_stopper_opt {
                info!("stopping node {:?} ...", node_id);
                if let Err(err) = node_stopper.stop_node() {
                    error!("could not stop node {:?}: {:?}", node_id, err);
                }
                info!("stopping node {:?}...done", node_id);
            }
        }
    }

    /// Move all of the [`NodeStopper`] objects out of the `node_infos` tracker and return them.
    fn take_node_stoppers(&self) -> Vec<(NodeId, Option<NodeStopper>)> {
        let mut node_infos = self
            .node_infos
            .write()
            .expect("could not acquire lock on node_infos");
        node_infos
            .iter_mut()
            .map(|(id, info)| (*id, info.node_stopper.take()))
            .collect()
    }

    /// Notify all Nodes that are waiting on any channels to wake up.
    fn notify_all_waiters(&self) {
        // Hold the write lock and wake up any Node threads blocked on a `Channel`.
        let node_infos = self
            .node_infos
            .read()
            .expect("could not acquire lock on node_infos");
        for node_id in node_infos.keys().sorted() {
            let node_info = node_infos.get(node_id).unwrap();
            for (handle, half) in &node_info.abi_handles {
                debug!(
                    "waking waiters on {:?} handle {} => {:?}",
                    node_id, handle, half
                );
                half.wake_waiters();
            }
        }
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

    /// Returns the least restrictive (i.e. least confidential, most trusted) label that this Node
    /// may downgrade `initial_label` to. This takes into account all the [downgrade
    /// privilege](NodeInfo::privilege) that the node possesses.
    fn get_node_downgraded_label(&self, node_id: NodeId, initial_label: &Label) -> Label {
        // Retrieve the set of tags that the node may downgrade.
        let node_privilege = self.get_node_privilege(node_id);
        Label {
            // Remove all the confidentiality tags that the Node may declassify.
            confidentiality_tags: initial_label
                .confidentiality_tags
                .iter()
                .filter(|t| {
                    !node_privilege
                        .can_declassify_confidentiality_tags
                        .contains(t)
                })
                .cloned()
                .collect(),
            // Add all the integrity tags that the Node may endorse.
            integrity_tags: initial_label
                .integrity_tags
                .iter()
                .chain(node_privilege.can_endorse_integrity_tags.iter())
                .cloned()
                .collect(),
        }
    }

    /// Returns a clone of the [`NodePrivilege`] of the provided Node.
    fn get_node_privilege(&self, node_id: NodeId) -> NodePrivilege {
        let node_infos = self
            .node_infos
            .read()
            .expect("could not acquire lock on node_infos");
        let node_info = node_infos.get(&node_id).expect("invalid node_id");
        node_info.privilege.clone()
    }

    /// Returns a clone of the [`Label`] associated with the provided reader `channel_half`.
    ///
    /// Returns an error if `channel_half` is not a valid read half.
    fn get_reader_channel_label(&self, channel_half: &ChannelHalf) -> Result<Label, OakStatus> {
        with_reader_channel(channel_half, |channel| Ok(channel.label.clone()))
    }

    /// Returns a clone of the [`Label`] associated with the provided writer `channel_half`.
    ///
    /// Returns an error if `channel_half` is not a valid write half.
    fn get_writer_channel_label(&self, channel_half: &ChannelHalf) -> Result<Label, OakStatus> {
        with_writer_channel(channel_half, |channel| Ok(channel.label.clone()))
    }

    /// Returns whether the given Node is allowed to read from the provided channel read half,
    /// according to their respective [`Label`]s.
    fn validate_can_read_from_channel(
        &self,
        node_id: NodeId,
        channel_half: &ChannelHalf,
    ) -> Result<(), OakStatus> {
        let channel_label = self.get_reader_channel_label(&channel_half)?;
        self.validate_can_read_from_label(node_id, &channel_label)
    }

    /// Returns whether the given Node is allowed to read from an entity with the provided
    /// [`Label`], taking into account all the [downgrade privilege](NodeInfo::privilege) the Node
    /// possesses.
    fn validate_can_read_from_label(
        &self,
        node_id: NodeId,
        source_label: &Label,
    ) -> Result<(), OakStatus> {
        // When reading from a Channel, we downgrade the Label of the Channel from which the Node is
        // reading: the thing being downgraded is the data being read into the Node (protected by
        // the Channel Label).
        let downgraded_source_label = self.get_node_downgraded_label(node_id, source_label);
        let target_label = self.get_node_label(node_id);
        trace!("{:?}: original source label: {:?}?", node_id, source_label);
        trace!(
            "{:?}: downgraded source label: {:?}?",
            node_id,
            downgraded_source_label
        );
        trace!("{:?}: target label: {:?}?", node_id, target_label);
        if downgraded_source_label.flows_to(&target_label) {
            trace!("{:?}: can read from {:?}", node_id, source_label);
            Ok(())
        } else {
            debug!("{:?}: cannot read from {:?}", node_id, source_label);
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Returns whether the given Node is allowed to write to the provided channel write half,
    /// according to their respective [`Label`]s.
    fn validate_can_write_to_channel(
        &self,
        node_id: NodeId,
        channel_half: &ChannelHalf,
    ) -> Result<(), OakStatus> {
        let channel_label = self.get_writer_channel_label(&channel_half)?;
        self.validate_can_write_to_label(node_id, &channel_label)
    }

    /// Returns whether the given Node is allowed to write to an entity with the provided [`Label`],
    /// taking into account all the [downgrade privilege](NodeInfo::privilege) the Node possesses.
    fn validate_can_write_to_label(
        &self,
        node_id: NodeId,
        target_label: &Label,
    ) -> Result<(), OakStatus> {
        // When writing to a Channel, we downgrade the Label of the Node itself: the thing being
        // downgraded is the data inside the Node (protected by the Node Label).
        let source_label = self.get_node_label(node_id);
        let downgraded_source_label = self.get_node_downgraded_label(node_id, &source_label);
        trace!("{:?}: original source label: {:?}?", node_id, source_label);
        trace!(
            "{:?}: downgraded source label: {:?}?",
            node_id,
            downgraded_source_label
        );
        trace!("{:?}: target label: {:?}?", node_id, target_label);
        if downgraded_source_label.flows_to(&target_label) {
            trace!("{:?}: can write to {:?}", node_id, target_label);
            Ok(())
        } else {
            warn!("{:?}: cannot write to {:?}", node_id, target_label);
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Creates a new [`Channel`] and returns a `(writer, reader)` pair of `oak_abi::Handle`s.
    ///
    /// [`Channel`]: crate::runtime::channel::Channel
    fn channel_create(
        &self,
        node_id: NodeId,
        label: &Label,
    ) -> Result<(oak_abi::Handle, oak_abi::Handle), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        // The label (and mere presence) of the newly created Channel is effectively public, so we
        // must ensure that the label of the calling Node flows to both "public untrusted" and to
        // the label of the Channel to be created.
        self.validate_can_write_to_label(node_id, &Label::public_untrusted())?;
        // We also additionally make sure that the label of the newly created Channel can be written
        // to by the current Node, since in general this may be lower than "public untrusted".
        self.validate_can_write_to_label(node_id, label)?;

        // First get a pair of `ChannelHalf` objects.
        let channel_id = self.next_channel_id.fetch_add(1, SeqCst);
        let channel = Channel::new(channel_id, label);
        let write_half = ChannelHalf::new(channel.clone(), ChannelHalfDirection::Write);
        let read_half = ChannelHalf::new(channel, ChannelHalfDirection::Read);
        trace!(
            "{:?}: allocated channel with halves w={:?},r={:?}",
            node_id,
            write_half,
            read_half,
        );
        // Insert them into the handle table and return the ABI handles to the caller.
        let write_handle = self.new_abi_handle(node_id, write_half);
        let read_handle = self.new_abi_handle(node_id, read_half);
        trace!(
            "{:?}: allocated handles w={}, r={} for channel",
            node_id,
            write_handle,
            read_handle,
        );
        Ok((write_handle, read_handle))
    }

    /// Reads the readable statuses for a slice of `ChannelHalf`s.
    fn readers_statuses(&self, node_id: NodeId, readers: &[ChannelHalf]) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|half| {
                self.channel_status(node_id, half)
                    .unwrap_or(ChannelReadStatus::InvalidChannel)
            })
            .collect()
    }

    /// Given a slice of `ChannelHalf`s representing channel read handles:
    /// - If the [`Runtime`] is terminating this will return immediately with an `ErrTerminated`
    ///   status.
    /// - If any of the channels is in an erroneous status, e.g. when a channel is orphaned, this
    ///   will immediately return with all the channels statuses set in the returned vector.
    /// - If all channels are in a good status but no messages are available on any of the channels
    ///   (i.e., all channels have status [`ChannelReadStatus::NotReady`]),
    ///   [`Runtime::wait_on_channels`] blocks until a message is available on one of the channels,
    ///   or one of the channels is orphaned. In both cases a vector of all the channels statuses
    ///   will be returned, unless the [`Runtime`] is terminating, in which case
    ///   `Err(ErrTerminated)` will be returned.
    ///
    /// Invariant: The returned vector of [`ChannelReadStatus`] values will be in 1-1
    /// correspondence with the passed-in vector of [`oak_abi::Handle`]s.
    ///
    /// See also the host ABI function
    /// [`wait_on_channels`](https://github.com/project-oak/oak/blob/main/docs/abi.md#wait_on_channels).
    ///
    /// [`Runtime`]: crate::runtime::Runtime
    fn wait_on_channels(
        &self,
        node_id: NodeId,
        read_handles: &[oak_abi::Handle],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        // Accumulate both the valid channels and their original position.
        let mut all_statuses = vec![ChannelReadStatus::InvalidChannel; read_handles.len()];
        let mut reader_pos = Vec::new();
        let mut readers = Vec::new();
        for (i, handle) in read_handles.iter().enumerate() {
            if let Ok(half) = self.abi_to_read_half(node_id, *handle) {
                reader_pos.push(i);
                readers.push(half);
            }
        }

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

            let thread_ref = Arc::new(thread.clone());

            for reader in &readers {
                with_reader_channel(reader, |channel| {
                    channel.add_waiter(&thread_ref);
                    Ok(())
                })?;
            }
            let statuses = self.readers_statuses(node_id, &readers);
            // Transcribe the status for valid channels back to the original position
            // in the list of all statuses.
            for i in 0..readers.len() {
                all_statuses[reader_pos[i]] = statuses[i];
            }

            let all_not_ready = statuses.iter().all(|&s| s == ChannelReadStatus::NotReady);

            if !all_not_ready || read_handles.is_empty() || readers.len() != read_handles.len() {
                return Ok(all_statuses);
            }

            debug!(
                "{:?}: wait_on_channels: channels not ready, parking thread {:?}",
                node_id,
                thread::current()
            );

            thread::park();

            debug!(
                "{:?}: wait_on_channels: thread {:?} re-woken",
                node_id,
                thread::current()
            );
        }
        Err(OakStatus::ErrTerminated)
    }

    /// Write a message to a channel. Fails with [`OakStatus::ErrChannelClosed`] if the underlying
    /// channel has been orphaned.
    fn channel_write(
        &self,
        node_id: NodeId,
        write_handle: oak_abi::Handle,
        node_msg: NodeMessage,
    ) -> Result<(), OakStatus> {
        let half = self.abi_to_write_half(node_id, write_handle)?;
        self.validate_can_write_to_channel(node_id, &half)?;

        // Translate the Node-relative handles in the `NodeMessage` to channel halves.
        let msg = self.message_from(node_msg, node_id)?;
        with_writer_channel(&half, |channel| {
            if !channel.has_readers() {
                return Err(OakStatus::ErrChannelClosed);
            }
            channel.messages.write().unwrap().push_back(msg);
            channel.wake_waiters();

            Ok(())
        })
    }

    /// Translate the Node-relative handles in the `NodeMessage` to channel halves.
    fn message_from(&self, node_msg: NodeMessage, node_id: NodeId) -> Result<Message, OakStatus> {
        Ok(Message {
            data: node_msg.data,
            channels: node_msg
                .handles
                .into_iter()
                .map(|handle| self.abi_to_half(node_id, handle))
                .collect::<Result<Vec<ChannelHalf>, OakStatus>>()?,
        })
    }

    /// Read a message from a channel. Fails with [`OakStatus::ErrChannelClosed`] if
    /// the underlying channel is empty and has been orphaned.
    fn channel_read(
        &self,
        node_id: NodeId,
        read_handle: oak_abi::Handle,
    ) -> Result<Option<NodeMessage>, OakStatus> {
        let half = self.abi_to_read_half(node_id, read_handle)?;
        self.validate_can_read_from_channel(node_id, &half)?;
        match with_reader_channel(&half, |channel| {
            match channel.messages.write().unwrap().pop_front() {
                Some(m) => Ok(Some(m)),
                None => {
                    if !channel.has_writers() {
                        Err(OakStatus::ErrChannelClosed)
                    } else {
                        Ok(None)
                    }
                }
            }
        }) {
            Err(status) => Err(status),
            Ok(None) => Ok(None),
            Ok(Some(runtime_msg)) => Ok(Some(self.node_message_from(runtime_msg, node_id))),
        }
    }

    /// Determine the readable status of a channel, returning:
    /// - `Ok`([`ChannelReadStatus::ReadReady`]) if there is at least one message in the channel.
    /// - `Ok`([`ChannelReadStatus::Orphaned`]) if there are no messages and there are no writers.
    /// - `Ok`([`ChannelReadStatus::NotReady`]) if there are no messages but there are some writers.
    /// - `Ok`([`ChannelReadStatus::PermissionDenied`]) if the node does not have permission to read
    ///   from the channel.
    /// - `Err`([`OakStatus::ErrBadHandle`]) if the input handle does not indicate the read half of
    ///   a channel.
    fn channel_status(
        &self,
        node_id: NodeId,
        half: &ChannelHalf,
    ) -> Result<ChannelReadStatus, OakStatus> {
        if let Err(OakStatus::ErrPermissionDenied) =
            self.validate_can_read_from_channel(node_id, half)
        {
            return Ok(ChannelReadStatus::PermissionDenied);
        };
        with_reader_channel(half, |channel| {
            Ok(if channel.messages.read().unwrap().front().is_some() {
                ChannelReadStatus::ReadReady
            } else if !channel.has_writers() {
                ChannelReadStatus::Orphaned
            } else {
                ChannelReadStatus::NotReady
            })
        })
    }

    /// Reads a message from the channel if `bytes_capacity` and `handles_capacity` are large
    /// enough to accept the message. Fails with `OakStatus::ErrChannelClosed` if the underlying
    /// channel has been orphaned _and_ is empty. If there was not enough `bytes_capacity` or
    /// `handles_capacity`, `try_read_message` returns the required capacity values in
    /// `Some(NodeReadStatus::NeedsCapacity(needed_bytes_capacity,needed_handles_capacity))`. Does
    /// not guarantee that the next call will succeed after capacity adjustments as another Node
    /// may have read the original message.
    fn channel_try_read_message(
        &self,
        node_id: NodeId,
        handle: oak_abi::Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<NodeReadStatus>, OakStatus> {
        let half = self.abi_to_read_half(node_id, handle)?;
        self.validate_can_read_from_channel(node_id, &half)?;
        let result = with_reader_channel(&half, |channel| {
            let mut messages = channel.messages.write().unwrap();
            match messages.front() {
                Some(front) => {
                    let req_bytes_capacity = front.data.len();
                    let req_handles_capacity = front.channels.len();

                    if req_bytes_capacity > bytes_capacity
                        || req_handles_capacity > handles_capacity
                    {
                        Ok(Some(ReadStatus::NeedsCapacity(
                            req_bytes_capacity,
                            req_handles_capacity,
                        )))
                    } else {
                        Ok(Some(ReadStatus::Success(messages.pop_front().expect(
                            "Front element disappeared while we were holding the write lock!",
                        ))))
                    }
                }
                None => {
                    if !channel.has_writers() {
                        Err(OakStatus::ErrChannelClosed)
                    } else {
                        Ok(None)
                    }
                }
            }
        })?;
        // Translate the result into the handle numbering space of this Node.
        Ok(match result {
            None => None,
            Some(ReadStatus::NeedsCapacity(z, c)) => Some(NodeReadStatus::NeedsCapacity(z, c)),
            Some(ReadStatus::Success(msg)) => Some(NodeReadStatus::Success(
                self.node_message_from(msg, node_id),
            )),
        })
    }

    /// Translate a Message to include ABI handles (which are relative to this Node) rather than
    /// internal channel references.
    fn node_message_from(&self, msg: Message, node_id: NodeId) -> NodeMessage {
        NodeMessage {
            data: msg.data,
            handles: msg
                .channels
                .iter()
                .map(|half| self.new_abi_handle(node_id, half.clone()))
                .collect(),
        }
    }

    /// Close an [`oak_abi::Handle`], potentially orphaning the underlying [`channel::Channel`].
    fn channel_close(&self, node_id: NodeId, handle: oak_abi::Handle) -> Result<(), OakStatus> {
        // Remove the ABI handle -> half mapping; half will be dropped at end of scope.
        self.drop_abi_handle(node_id, handle)?;
        Ok(())
    }

    /// Create a fresh [`NodeId`].
    fn new_node_id(&self) -> NodeId {
        NodeId(self.next_node_id.fetch_add(1, SeqCst))
    }

    /// Remove a Node by [`NodeId`] from the [`Runtime`].
    fn remove_node_id(&self, node_id: NodeId) {
        // Close any remaining handles
        let remaining_handles: Vec<_> = {
            let node_infos = self.node_infos.read().unwrap();
            let node_info = node_infos
                .get(&node_id)
                .unwrap_or_else(|| panic!("remove_node_id: No such node_id {:?}", node_id));
            node_info.abi_handles.keys().copied().collect()
        };

        debug!(
            "{:?}: remove_node_id() found open handles on exit: {:?}",
            node_id, remaining_handles
        );

        for handle in remaining_handles {
            self.channel_close(node_id, handle)
                .expect("remove_node_id: Unable to close hanging channel!");
        }

        self.node_infos
            .write()
            .unwrap()
            .remove(&node_id)
            .expect("remove_node_id: Node didn't exist!");
        self.update_nodes_count_metric();
    }

    /// Add an [`NodeId`] [`NodeInfo`] pair to the [`Runtime`]. This method temporarily holds the
    /// [`Runtime::node_infos`] write lock.
    fn add_node_info(&self, node_id: NodeId, node_info: NodeInfo) {
        self.node_infos
            .write()
            .expect("could not acquire lock on node_infos")
            .insert(node_id, node_info);
        self.update_nodes_count_metric();
    }

    /// Add the [`NodeStopper`] for a running Node to `NodeInfo`.
    /// The provided [`NodeId`] value must already be present in [`Runtime::node_infos`].
    fn add_node_stopper(&self, node_id: NodeId, node_stopper: NodeStopper) {
        let mut node_infos = self
            .node_infos
            .write()
            .expect("could not acquire lock on node_infos");
        let mut node_info = node_infos
            .get_mut(&node_id)
            .expect("node ID not in node_infos");
        assert!(node_info.node_stopper.is_none());
        node_info.node_stopper = Some(node_stopper);
    }

    /// Create a Node within the [`Runtime`] corresponding to a given module name and
    /// entrypoint. The channel identified by `initial_handle` is installed in the new
    /// Node's handle table and the new handle value is passed to the newly created Node.
    ///
    /// The caller also specifies a [`Label`], which is assigned to the newly created Node. See
    /// <https://github.com/project-oak/oak/blob/main/docs/concepts.md#labels> for more
    /// information on labels.
    ///
    /// This method is defined on [`Arc`] and not [`Runtime`] itself, so that
    /// the [`Arc`] can clone itself and be included in a [`RuntimeProxy`] object
    /// to be given to a new Node instance.
    fn node_create(
        self: Arc<Self>,
        node_id: NodeId,
        config: &NodeConfiguration,
        label: &Label,
        initial_handle: oak_abi::Handle,
    ) -> Result<(), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        // The label (and mere presence) of the newly created Node is effectively public, so we must
        // ensure that the label of the calling Node flows to both "public untrusted" and to the
        // label of the Node to be created.
        self.validate_can_write_to_label(node_id, &Label::public_untrusted())?;
        // We also additionally make sure that the label of the newly created Node can be written to
        // by the current Node, since in general this may be lower than "public untrusted".
        self.validate_can_write_to_label(node_id, label)?;

        let reader = self.abi_to_read_half(node_id, initial_handle)?;

        let new_node_proxy = self.clone().proxy_for_new_node();
        let new_node_id = new_node_proxy.node_id;
        let new_node_name = format!("{}({})", config.name, new_node_id.0);

        // This only creates a Node instance, but does not start it.
        let instance = node::create_node(
            &self.application_configuration,
            config,
            &self.grpc_configuration,
        )
        .map_err(|err| {
            warn!("could not create node: {:?}", err);
            OakStatus::ErrInvalidArgs
        })?;

        let node_privilege = instance.get_privilege();

        self.node_configure_instance(new_node_id, &new_node_name, label, &node_privilege);
        let initial_handle = new_node_proxy
            .runtime
            .new_abi_handle(new_node_proxy.node_id, reader);

        info!(
            "{:?}: start node instance {:?} with privilege {:?}",
            node_id, new_node_id, node_privilege
        );
        let node_stopper = self.clone().node_start_instance(
            &new_node_name,
            instance,
            new_node_proxy,
            initial_handle,
        )?;

        // Insert the now running instance to the list of running instances (by moving it), so that
        // `Node::stop` will be called on it eventually.
        self.add_node_stopper(new_node_id, node_stopper);

        {
            // Fire NodeCreated introspection event
            let NodeId(node_id_as_primitive) = new_node_id;
            let event_details = NodeCreated {
                node_id: node_id_as_primitive,
            };

            self.introspection_event(EventDetails::NodeCreated(event_details));
        }

        Ok(())
    }

    /// Starts running a newly created Node instance on a new thread.
    /// The `node_name` parameter is only used for diagnostic/debugging output.
    fn node_start_instance(
        self: Arc<Self>,
        node_name: &str,
        node_instance: Box<dyn crate::node::Node>,
        node_proxy: RuntimeProxy,
        initial_handle: oak_abi::Handle,
    ) -> Result<NodeStopper, OakStatus> {
        // Try to start the Node instance.
        //
        // In order for this to work correctly, the `NodeInfo` entry must already exist in
        // `Runtime`, which is why we could not start this instance before the call to
        // `Runtime::add_node_info` above.
        //
        // On the other hand, we also cannot start it after the call to `Runtime::add_node_instance`
        // below, because that takes ownership of the instance itself.
        //
        // We also want no locks to be held while the instance is starting.
        let node_id = node_proxy.node_id;
        let (node_notify_sender, node_notify_receiver) = tokio::sync::oneshot::channel::<()>();
        let node_join_handle = thread::Builder::new()
            .name(node_name.to_string())
            .spawn(move || {
                node_instance.run(node_proxy, initial_handle, node_notify_receiver);
                // It's now safe to remove the state for this Node, as there's nothing left
                // that can invoke `Runtime` functionality for it.
                self.remove_node_id(node_id)
            })
            .expect("failed to spawn thread");
        // Note: self has been moved into the thread running the closure.

        Ok(NodeStopper {
            node_name: node_name.to_string(),
            join_handle: node_join_handle,
            notify_sender: node_notify_sender,
        })
    }

    /// Configure data structures for a Node instance.
    fn node_configure_instance(
        &self,
        node_id: NodeId,
        node_name: &str,
        label: &Label,
        privilege: &NodePrivilege,
    ) {
        self.add_node_info(
            node_id,
            NodeInfo {
                name: node_name.to_string(),
                label: label.clone(),
                privilege: privilege.clone(),
                abi_handles: HashMap::new(),
                node_stopper: None,
            },
        );
    }

    /// Create a [`RuntimeProxy`] instance for a new Node, creating the new [`NodeId`]
    /// value along the way.
    fn proxy_for_new_node(self: Arc<Self>) -> RuntimeProxy {
        RuntimeProxy {
            runtime: self.clone(),
            node_id: self.new_node_id(),
        }
    }

    /// Update the node count metric with the current value.
    fn update_nodes_count_metric(&self) {
        self.metrics_data
            .runtime_metrics
            .runtime_nodes_total
            .set(self.get_nodes_count());
    }

    fn get_nodes_count(&self) -> i64 {
        self.node_infos
            .read()
            .expect("could not acquire lock on node_infos")
            .len() as i64
    }
}
