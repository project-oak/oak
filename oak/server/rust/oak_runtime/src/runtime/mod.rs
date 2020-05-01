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

use core::sync::atomic::{AtomicBool, AtomicU64, Ordering::SeqCst};
use itertools::Itertools;
use log::{debug, error, info, trace};
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    string::String,
    sync::{Arc, Mutex, RwLock},
    thread,
    thread::JoinHandle,
};

use crate::{message::Message, metrics::METRICS, node, pretty_name_for_thread};
use oak_abi::{label::Label, ChannelReadStatus, OakStatus};

mod channel;
#[cfg(feature = "oak_debug")]
mod introspect;
#[cfg(test)]
mod tests;

pub use channel::{Handle, HandleDirection};

/// Trait that gives an identifier for a data structure that is suitable for
/// use with Graphviz/Dot.
pub trait DotIdentifier {
    fn dot_id(&self) -> String;
}

/// Trait that returns the path at which the debug introspection server will
/// show a page for a data structure.
pub trait HtmlPath {
    fn html_path(&self) -> String;
}

struct NodeInfo {
    /// Name for the Node in debugging output.
    pretty_name: String,

    /// The Label associated with this Node.
    ///
    /// This is set at Node creation time and does not change after that.
    ///
    /// See https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels
    label: Label,

    /// A [`HashSet`] containing all the handles associated with this Node.
    // TODO(#777): this overlaps ChannelMapping.{reader,writer}
    handles: HashSet<Handle>,
}

impl std::fmt::Debug for NodeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "NodeInfo {{'{}', label={:?}, handles=[",
            self.pretty_name, self.label
        )?;
        write!(
            f,
            "{}",
            self.handles
                .iter()
                .map(|handle| format!("{:?}", handle))
                .join(", ")
        )?;
        write!(f, "]}}")
    }
}

/// An identifier for a Node that is opaque for type safety.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, PartialOrd, Ord)]
pub struct NodeId(pub u64);

impl DotIdentifier for NodeId {
    fn dot_id(&self) -> String {
        format!("node{}", self.0)
    }
}

impl HtmlPath for NodeId {
    fn html_path(&self) -> String {
        format!("/node/{}", self.0)
    }
}

/// A Node identifier reserved for the Runtime that allows access to all handles and channels.
// TODO(#724): make private once main() is in Rust not C++
pub const RUNTIME_NODE_ID: NodeId = NodeId(0);

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

/// Information for managing an associated server.
pub struct AuxServer {
    pub name: String,
    pub join_handle: Option<JoinHandle<()>>,
    pub notify_sender: Option<tokio::sync::oneshot::Sender<()>>,
}

impl AuxServer {
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
    fn drop(&mut self) {
        let join_handle = self.join_handle.take();
        let notify_sender = self.notify_sender.take();
        if let Some(notify_sender) = notify_sender {
            info!("stopping {} server", self.name);
            notify_sender.send(()).unwrap();
        }
        if let Some(join_handle) = join_handle {
            let result = join_handle.join();
            info!("stopped {} server, result {:?}", self.name, result);
        }
    }
}

/// Runtime structure for configuring and running a set of Oak Nodes.
pub struct Runtime {
    configuration: Configuration,
    terminating: AtomicBool,

    channels: channel::ChannelMapping,

    /// Runtime-specific state for each Node instance.
    node_infos: RwLock<HashMap<NodeId, NodeInfo>>,

    /// [`JoinHandle`]s of the currently running Node instances, so that [`Runtime::stop`] can wait
    /// for termination of all of them.
    node_join_handles: Mutex<HashMap<NodeId, JoinHandle<()>>>,

    next_node_id: AtomicU64,

    aux_servers: Mutex<Vec<AuxServer>>,
}

impl Runtime {
    /// Creates a [`Runtime`] instance but does not start executing any Node.
    pub fn create(configuration: Configuration) -> Self {
        Self {
            configuration,
            terminating: AtomicBool::new(false),
            channels: channel::ChannelMapping::new(),

            node_infos: RwLock::new(HashMap::new()),
            node_join_handles: Mutex::new(HashMap::new()),

            // NodeId(0) reserved for RUNTIME_NODE_ID.
            next_node_id: AtomicU64::new(1),

            aux_servers: Mutex::new(Vec::new()),
        }
    }

    /// Configures and runs the protobuf specified Application [`Configuration`].
    ///
    /// After starting a [`Runtime`], calling [`Runtime::stop`] will send termination signals to
    /// Nodes and wait for them to terminate.
    ///
    /// Returns a writeable [`Handle`] to send messages into the [`Runtime`]. To receive messages,
    /// creating a new channel and passing the write [`Handle`] into the Runtime will enable
    /// messages to be read back out.
    pub fn run(
        self: Arc<Self>,
        runtime_config: crate::RuntimeConfiguration,
    ) -> Result<Handle, OakStatus> {
        let module_name = self.configuration.entry_module.clone();
        let entrypoint = self.configuration.entrypoint.clone();

        if cfg!(feature = "oak_debug") {
            if let Some(port) = runtime_config.introspect_port {
                self.aux_servers.lock().unwrap().push(AuxServer::new(
                    "introspect",
                    port,
                    self.clone(),
                    introspect::serve,
                ));
            }
        }
        if let Some(port) = runtime_config.metrics_port {
            self.aux_servers.lock().unwrap().push(AuxServer::new(
                "metrics",
                port,
                self.clone(),
                crate::metrics::server::start_metrics_server,
            ));
        }

        // When first starting, we assign the least privileged label to the channel connecting the
        // outside world to the entry point Node.
        let (chan_writer, chan_reader) =
            self.new_channel(RUNTIME_NODE_ID, &Label::public_trusted());

        self.clone().node_create(
            RUNTIME_NODE_ID,
            &module_name,
            &entrypoint,
            // When first starting, we assign the least privileged label to the entry point Node.
            &Label::public_trusted(),
            chan_reader,
        )?;

        // We call `expect` here because this should never fail, since the channel was just created
        // and guaranteed not to have already been closed.
        self.channel_close(RUNTIME_NODE_ID, chan_reader)
            .expect("could not close channel");

        Ok(chan_writer)
    }

    /// Generate a Graphviz dot graph that shows the current shape of the Nodes and Channels in
    /// the runtime.
    #[cfg(feature = "oak_debug")]
    pub fn graph(&self) -> String {
        let mut s = String::new();
        writeln!(&mut s, "digraph Runtime {{").unwrap();
        // Graph nodes for Oak Nodes.
        {
            writeln!(&mut s, "  {{").unwrap();
            writeln!(
                &mut s,
                "    node [shape=box style=filled fillcolor=red fontsize=24]"
            )
            .unwrap();
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                write!(
                    &mut s,
                    r###"    {} [label="{}" URL="{}"]"###,
                    node_id.dot_id(),
                    node_info.pretty_name,
                    node_id.html_path(),
                )
                .unwrap();
                if self
                    .node_join_handles
                    .lock()
                    .unwrap()
                    .get(&node_id)
                    .is_none()
                {
                    write!(&mut s, " [style=dashed]").unwrap();
                }
                writeln!(&mut s).unwrap();
            }
            writeln!(&mut s, "  }}").unwrap();
        }

        // Graph nodes for internal connections between Nodes and Channels.
        write!(&mut s, "{}", self.channels.graph_nodes()).unwrap();

        // Edges for connections between Nodes and channel halves.  Track which we have seen.
        let mut seen = HashSet::new();
        {
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                for half_id in &node_info.handles {
                    seen.insert(*half_id);
                    match self.channel_get_direction(*node_id, *half_id).unwrap() {
                        HandleDirection::Write => {
                            writeln!(&mut s, "  {} -> {}", node_id.dot_id(), half_id.dot_id())
                                .unwrap();
                        }
                        HandleDirection::Read => {
                            writeln!(&mut s, "  {} -> {}", half_id.dot_id(), node_id.dot_id())
                                .unwrap();
                        }
                    }
                }
            }
        }
        // Edges for connections between halves and Channels.
        write!(&mut s, "{}", self.channels.graph_edges(seen)).unwrap();
        writeln!(&mut s, "}}").unwrap();
        s
    }

    #[cfg(feature = "oak_debug")]
    pub fn html(&self) -> String {
        let mut s = String::new();
        writeln!(&mut s, "<h2>Nodes</h2>").unwrap();
        writeln!(&mut s, r###"<p><a href="/graph">Show as graph</a><ul>"###).unwrap();
        {
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                write!(
                    &mut s,
                    r###"<li><a href="{}">{:?}</a> => <tt>{:?}"###,
                    node_id.html_path(),
                    node_id,
                    node_info
                )
                .unwrap();
                if let Some(join_handle) = self.node_join_handles.lock().unwrap().get(&node_id) {
                    write!(&mut s, ", join_handle={:?}", join_handle).unwrap();
                }
                writeln!(&mut s, "</tt>").unwrap();
            }
        }
        writeln!(&mut s, "</ul>").unwrap();
        write!(&mut s, "{}", self.channels.html()).unwrap();
        s
    }

    #[cfg(feature = "oak_debug")]
    pub fn html_for_node(&self, id: u64) -> Option<String> {
        let node_id = NodeId(id);
        let node_infos = self.node_infos.read().unwrap();
        let node_info = node_infos.get(&node_id)?;
        let mut s = String::new();
        write!(&mut s, "<h2>{}</h2>", node_info.pretty_name).unwrap();
        if let Some(join_handle) = self.node_join_handles.lock().unwrap().get(&node_id) {
            write!(
                &mut s,
                "<p>Node thread is currently running, join_handle={:?}",
                join_handle
            )
            .unwrap();
        } else {
            write!(&mut s, "<p>No current thread for Node.").unwrap();
        }
        write!(&mut s, "<p>Label={:?}<p>Handles:<ul>", node_info.label).unwrap();
        for half_id in &node_info.handles {
            write!(
                &mut s,
                r###"<li><a href="{}">{:?}</a>"###,
                half_id.html_path(),
                half_id
            )
            .unwrap();
        }
        Some(s)
    }
    #[cfg(feature = "oak_debug")]
    pub fn html_for_channel(&self, id: u64) -> Option<String> {
        self.channels.html_for_channel(id)
    }
    #[cfg(feature = "oak_debug")]
    pub fn html_for_half(&self, id: u64) -> Option<String> {
        self.channels.html_for_half(id)
    }

    /// Thread safe method for determining if the [`Runtime`] is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Thread safe method for signaling termination to a [`Runtime`] and waiting for its Node
    /// threads to terminate.
    pub fn stop(&self) {
        info!("stopping runtime instance");

        // Terminate any running servers.
        self.aux_servers.lock().unwrap().drain(..);

        // Set the terminating flag; this will prevent additional Nodes from starting to wait again,
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

        // Wait for the main thread of each Node to finish. Any thread that was blocked on
        // `wait_on_channels` is now unblocked and received `OakStatus::ErrTerminated`, so we wait
        // for any additional work to be finished here. This may take an arbitrary amount of time,
        // depending on the work that the Node thread has to perform, but at least we know that the
        // it will not be able to enter again in a blocking state.
        for (_, instance) in self
            .node_join_handles
            .lock()
            .expect("could not acquire lock on node_join_handles")
            .drain()
        {
            if let Err(err) = instance.join() {
                error!("could not terminate node: {:?}", err);
            }
        }
    }

    /// Allow the corresponding [`Node`] to use the [`Handle`]s passed via the iterator.
    /// This is achieved by adding the [`Handle`]s to the [`Node`]s [`HashMap`] of [`Handle`]s.
    ///
    /// [`Node`]: crate::node::Node
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
        self.validate_handles_access(node_id, &[handle])
    }

    /// Validate the [`NodeId`] has access to all [`Handle`]'s passed in the iterator, returning
    /// `Err(OakStatus::ErrBadHandle)` if access is not allowed.
    fn validate_handles_access(
        &self,
        node_id: NodeId,
        handles: &[Handle],
    ) -> Result<(), OakStatus> {
        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            return Ok(());
        }

        let node_infos = self.node_infos.read().unwrap();
        let node_info = node_infos
            .get(&node_id)
            .expect("Invalid node_id passed into filter_optional_handles!");

        for handle in handles {
            // Check handle is accessible by the Node.
            if !node_info.handles.contains(&handle) {
                error!(
                    "{:?}: validate_handles_access(): handle {:?} not found",
                    node_id, handle
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
    /// order to limit the scope of holding the lock on [`channel::ChannelMapping::channels`].
    ///
    /// Returns an error if `channel_handle` is invalid.
    fn get_reader_channel_label(&self, channel_handle: Handle) -> Result<Label, OakStatus> {
        self.channels.with_channel(
            self.channels.get_reader_channel(channel_handle)?,
            |channel| Ok(channel.label.clone()),
        )
    }

    /// Returns a clone of the [`Label`] associated with the provided writer `channel_handle`, in
    /// order to limit the scope of holding the lock on [`channel::ChannelMapping::channels`].
    ///
    /// Returns an error if `channel_handle` is invalid.
    fn get_writer_channel_label(&self, channel_handle: Handle) -> Result<Label, OakStatus> {
        self.channels.with_channel(
            self.channels.get_writer_channel(channel_handle)?,
            |channel| Ok(channel.label.clone()),
        )
    }

    /// Returns whether the calling Node is allowed to read from the provided channel, according to
    /// their respective [`Label`]s.
    fn validate_can_read_from_channel(
        &self,
        node_id: NodeId,
        channel_handle: Handle,
    ) -> Result<(), OakStatus> {
        trace!(
            "{:?}: validating readability of {:?}",
            node_id,
            channel_handle
        );

        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            trace!("{:?}: runtime can read from any channel", node_id);
            return Ok(());
        }

        let node_label = self.get_node_label(node_id);
        let channel_label = self.get_reader_channel_label(channel_handle)?;
        trace!(
            "{:?}: node_label={:?}, channel_label={:?}",
            node_id,
            node_label,
            channel_label
        );
        if channel_label.flows_to(&node_label) {
            trace!("{:?}: can read from channel {:?}", node_id, channel_handle);
            Ok(())
        } else {
            debug!(
                "{:?}: cannot read from channel {:?}",
                node_id, channel_handle
            );
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Returns whether the calling Node is allowed to read from all the provided channels,
    /// according to their respective [`Label`]s.
    fn validate_can_read_from_channels(
        &self,
        node_id: NodeId,
        channel_handles: &[Handle],
    ) -> Result<(), OakStatus> {
        let all_channel_handles_ok = channel_handles.iter().all(|channel_handle| {
            self.validate_can_read_from_channel(node_id, *channel_handle)
                .is_ok()
        });
        if all_channel_handles_ok {
            Ok(())
        } else {
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Returns whether the calling Node is allowed to write to the provided channel, according to
    /// their respective [`Label`]s.
    fn validate_can_write_to_channel(
        &self,
        node_id: NodeId,
        channel_handle: Handle,
    ) -> Result<(), OakStatus> {
        trace!(
            "{:?}: validating writability of {:?}",
            node_id,
            channel_handle
        );

        // Allow RUNTIME_NODE_ID access to all handles.
        if node_id == RUNTIME_NODE_ID {
            trace!("{:?}: runtime can write to any channel", node_id);
            return Ok(());
        }

        let node_label = self.get_node_label(node_id);
        let channel_label = self.get_writer_channel_label(channel_handle)?;
        trace!(
            "{:?}: node_label={:?}, channel_label={:?}",
            node_id,
            node_label,
            channel_label
        );
        if node_label.flows_to(&channel_label) {
            trace!("{:?}: can write to channel {:?}", node_id, channel_handle);
            Ok(())
        } else {
            debug!(
                "{:?}: cannot write to channel {:?}",
                node_id, channel_handle
            );
            Err(OakStatus::ErrPermissionDenied)
        }
    }

    /// Creates a new [`Channel`] and returns a `(writer handle, reader handle)` pair.
    ///
    /// [`Channel`]: crate::runtime::channel::Channel
    pub fn new_channel(&self, node_id: NodeId, label: &Label) -> (Handle, Handle) {
        // TODO(#630): Check whether the calling Node can create a Node with the specified label.
        let (writer, reader) = self.channels.new_channel(label);
        self.track_handles_in_node(node_id, vec![writer, reader]);
        (writer, reader)
    }

    /// Reads the statuses from a slice of `Handle`s.
    /// [`ChannelReadStatus::InvalidChannel`] is set for `None` readers in the slice. For `Some(_)`
    /// readers, the result is set from a call to `has_message`.
    fn readers_statuses(&self, node_id: NodeId, readers: &[Handle]) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|chan| {
                self.channel_status(node_id, *chan)
                    .unwrap_or(ChannelReadStatus::InvalidChannel)
            })
            .collect()
    }

    /// Waits on a slice of `Handle`s, blocking until one of the following conditions:
    /// - If the [`Runtime`] is terminating this will return immediately with an `ErrTerminated`
    ///   status for each channel.
    /// - If all readers are in an erroneous status, e.g. when all channels are orphaned, this will
    ///   immediately return the channels statuses.
    /// - If any of the channels is able to read a message, the corresponding element in the
    ///   returned vector will be set to `Ok(ReadReady)`, with `Ok(NotReady)` signaling the channel
    ///   has no message available
    ///
    /// In particular, if there is at least one channel in good status and no messages on said
    /// channel available, [`Runtime::wait_on_channels`] will continue to block until a message is
    /// available.
    ///
    /// [`Runtime`]: crate::runtime::Runtime
    pub fn wait_on_channels(
        &self,
        node_id: NodeId,
        readers: &[Handle],
    ) -> Result<(Vec<ChannelReadStatus>, bool), OakStatus> {
        self.validate_handles_access(node_id, readers)?;
        self.validate_can_read_from_channels(node_id, readers)?;

        let thread = thread::current();
        while !self.is_terminating() {
            let statuses = self.readers_statuses(node_id, &readers);

            let any_invalid = statuses.iter().any(|&s| {
                s == ChannelReadStatus::InvalidChannel || s == ChannelReadStatus::Orphaned
            });

            if any_invalid {
                debug!(
                    "{:?}: wait_on_channels: Returning early with ChannelWaitStatus::HasInvalid.",
                    node_id
                );
                // return Ok(ChannelWaitStatus::HasInvalid(statuses));
                return Ok((statuses, false));
            }

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
                self.channels.with_channel(
                    self.channels.get_reader_channel(*reader)?,
                    |channel| {
                        channel.add_waiter(thread_id, &thread_ref);
                        Ok(())
                    },
                )?;
            }

            let any_ready = statuses.iter().any(|&s| s == ChannelReadStatus::ReadReady);

            if any_ready {
                return Ok((statuses, true));
            }

            debug!(
                "{:?}: wait_on_channels: channels not ready, parking thread {}",
                node_id,
                pretty_name_for_thread(&thread::current())
            );

            thread::park();

            debug!(
                "{:?}: wait_on_channels: thread {} re-woken",
                node_id,
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

        // Add handles outside the channels lock so we don't hold the node_infos lock inside the
        // channel lock.
        if let Ok(Some(ReadStatus::Success(ref msg))) = result {
            self.track_handles_in_node(node_id, msg.channels.clone());
        }

        result
    }

    /// Return the direction of a [`Handle`]. This is useful when reading
    /// [`Message`]s which contain [`Handle`]'s.
    pub fn channel_get_direction(
        &self,
        node_id: NodeId,
        reference: Handle,
    ) -> Result<HandleDirection, OakStatus> {
        self.validate_handle_access(node_id, reference)?;
        // TODO(#630): Check whether the calling Node can read from the specified handle. Currently,
        // performing this check seems to get tests to hang forever.
        self.channels.get_direction(reference)
    }
    /// Close a [`Handle`], potentially orphaning the underlying [`channel::Channel`].
    pub fn channel_close(&self, node_id: NodeId, reference: Handle) -> Result<(), OakStatus> {
        self.validate_handle_access(node_id, reference)?;

        if node_id != RUNTIME_NODE_ID {
            // Remove handle from the Node's available handles
            let mut node_infos = self.node_infos.write().unwrap();
            let node_info = node_infos
                .get_mut(&node_id)
                .expect("channel_close: No such node_id");
            node_info.handles.remove(&reference);
        }

        self.channels.remove_reference(reference)
    }

    /// Create a fresh [`NodeId`].
    fn new_node_id(&self) -> NodeId {
        NodeId(self.next_node_id.fetch_add(1, SeqCst))
    }

    /// Remove a Node by [`NodeId`] from the [`Runtime`].
    pub fn remove_node_id(&self, node_id: NodeId) {
        {
            // Do not remove the Node if it is RUNTIME_NODE_ID
            if node_id == RUNTIME_NODE_ID {
                return;
            }

            // Close any remaining handles
            let remaining_handles: Vec<_> = {
                let node_infos = self.node_infos.read().unwrap();
                let node_info = node_infos
                    .get(&node_id)
                    .unwrap_or_else(|| panic!("remove_node_id: No such node_id {:?}", node_id));
                node_info.handles.iter().copied().collect()
            };

            debug!(
                "{:?}: remove_node_id() found open channels on exit: {:?}",
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

    fn update_nodes_count_metric(&self) {
        METRICS.runtime_nodes_count.set(
            self.node_infos
                .read()
                .expect("could not acquire lock on node_infos")
                .len() as i64,
        );
    }

    /// Add an [`NodeId`] [`JoinHandle`] pair to the [`Runtime`]. This method temporarily holds the
    /// [`Runtime::node_join_handles`] lock.
    fn add_node_join_handle(&self, node_id: NodeId, node_join_handle: JoinHandle<()>) {
        self.node_join_handles
            .lock()
            .expect("could not acquire lock on node_join_handles")
            .insert(node_id, node_join_handle);
    }

    /// Thread safe method that attempts to create a Node within the [`Runtime`] corresponding to a
    /// given module name and entrypoint. The `reader: ChannelReader` is passed to the newly
    /// created Node.
    ///
    /// The caller also specifies a [`Label`], which is assigned to the newly created Node. See
    /// <https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels> for more
    /// information on labels.
    ///
    /// This method is defined on [`Arc`] and not [`Runtime`] itself, so that
    /// the [`Arc`] can clone itself and be included in a [`RuntimeProxy`] object
    /// to be given to a new Node.
    pub fn node_create(
        self: Arc<Self>,
        node_id: NodeId,
        module_name: &str,
        entrypoint: &str,
        label: &Label,
        reader: Handle,
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

        let node_id = self.new_node_id();
        let runtime_proxy = RuntimeProxy {
            runtime: self.clone(),
            node_id,
        };

        let reader = self.channels.duplicate_reference(reader)?;

        let instance = self
            .configuration
            .nodes
            .get(module_name)
            .ok_or(OakStatus::ErrInvalidArgs)
            .map(|conf| {
                // This only creates a Node instance, but does not start it.
                conf.create_node(module_name, runtime_proxy, entrypoint.to_owned(), reader)
            })?;

        self.node_start_instance(
            node_id,
            format!("{}.{}", module_name, entrypoint),
            instance,
            label,
            vec![reader],
        )?;

        Ok(())
    }

    /// Starts a newly created Node instance, by first initializing the necessary [`NodeInfo`] data
    /// structure in [`Runtime`], allowing it to access the provided [`Handle`]s, then calling
    /// [`Node::start`] on the instance, and finally storing a [`JoinHandle`] from the running
    /// instance in [`Runtime::node_join_handles`] so that it can later be terminated.  The
    /// `pretty_name` parameter is only used for diagnostic/debugging output.
    ///
    /// [`Node::start`]: crate::node::Node::start
    pub fn node_start_instance<I>(
        &self,
        node_id: NodeId,
        pretty_name: String,
        node_instance: Box<dyn crate::node::Node>,
        label: &Label,
        initial_handles: I,
    ) -> Result<(), OakStatus>
    where
        I: IntoIterator<Item = Handle>,
    {
        // First create the necessary info data structure in the Runtime, otherwise calls that the
        // Node makes to the Runtime during `Node::start` (synchronously or asynchronously) may
        // fail.
        self.add_node_info(
            node_id,
            NodeInfo {
                pretty_name,
                label: label.clone(),
                handles: HashSet::new(),
            },
        );

        // Make sure that the provided initial handles are tracked in the newly created Node from
        // the start.
        self.track_handles_in_node(node_id, initial_handles);

        // Try to start the Node instance, and store the join handle.
        //
        // In order for this to work correctly, the `NodeInfo` entry must already exist in
        // `Runtime`, which is why we could not start this instance before the call to
        // `Runtime::add_node_info` above.
        //
        // On the other hand, we also cannot start it after the call to `Runtime::add_node_instance`
        // below, because that takes ownership of the instance itself.
        //
        // We also want no locks to be held while the instance is starting.
        let node_join_handle = match node_instance.start() {
            Ok(join_handle) => join_handle,
            Err(status) => {
                self.remove_node_id(node_id);
                return Err(status);
            }
        };

        // Regardless of the result of `Node::start`, insert the now running instance to the list of
        // running instances (by moving it), so that `Node::stop` will be called on it eventually.
        self.add_node_join_handle(node_id, node_join_handle);

        // Return the result of `Node::start`.
        Ok(())
    }

    pub fn new_runtime_proxy(self: Arc<Self>) -> RuntimeProxy {
        RuntimeProxy {
            runtime: self.clone(),
            node_id: self.new_node_id(),
        }
    }
}

impl Drop for Runtime {
    fn drop(&mut self) {
        self.stop();
    }
}

/// A proxy object that binds together a reference to the underlying [`Runtime`] with a single
/// [`NodeId`].
///
/// This can be considered as the interface to the [`Runtime`] that Node and pseudo-Node
/// implementations have access to.
///
/// Each [`RuntimeProxy`] instance is used by an individual Node or pseudo-Node instance to
/// communicate with the [`Runtime`]. Nodes do not have direct access to the [`Runtime`] apart from
/// through [`RuntimeProxy`], which exposes a more limited API, and ensures that Nodes cannot
/// impersonate each other.
///
/// Individual methods simply forward to corresponding methods on the underlying [`Runtime`], by
/// partially applying the first argument.
#[derive(Clone)]
pub struct RuntimeProxy {
    pub runtime: Arc<Runtime>,
    pub node_id: NodeId,
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
        channel_read_handles: &[Handle],
    ) -> Result<(Vec<ChannelReadStatus>, bool), OakStatus> {
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
