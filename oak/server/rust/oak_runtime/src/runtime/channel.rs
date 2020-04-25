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

use itertools::Itertools;
use log::{debug, error};
use rand::RngCore;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Write,
    sync::{
        atomic::{AtomicU64, Ordering::SeqCst},
        Arc, Mutex, RwLock, Weak,
    },
    thread::{Thread, ThreadId},
};

use crate::{runtime::DotIdentifier, Message};
use oak_abi::OakStatus;

type Messages = VecDeque<Message>;

/// We use a `HashMap` keyed by `ThreadId` to prevent build up of stale `Weak<Thread>`s.
///
/// That is: If a thread waiting/blocked on a channel is woken by a different channel, its
/// `Weak<Thread>` will remain in the first channel's waiting_thread member. If a thread keeps
/// waiting on this first channel, and keeps being woken by other channels, it will keep re-adding
/// itself. We use a `HashMap` and insert at the current `ThreadId` so that we replace any stale
/// `Weak<Thread>`s which will have gone out of scope. (`wait_on_channels` drops the underlying arc
/// as soon as it is resumed.)
type WaitingThreads = Mutex<HashMap<ThreadId, Weak<Thread>>>;

/// The internal implementation of a channel representation backed by a `VecDeque<Message>`.
/// Readers and writers to this channel must increment the reader/writer count. This is implemented
/// for `ChannelWriter`/`ChannelReader`, which will increment/decrement readers/writers when
/// cloning/dropping.
pub struct Channel {
    pub messages: RwLock<Messages>,

    pub writers: AtomicU64,
    pub readers: AtomicU64,

    /// A HashMap of `ThreadId`s to `Weak<Thread>`s. This allows threads to insert a weak reference
    /// to themselves to be woken when a new message is available. Weak references are used so that
    /// if the thread is woken by a different channel, it can deallocate the underlying `Arc`
    /// instead of removing itself from all the `Channel`s it subscribed to.
    /// Threads can be woken up spuriously without issue.
    pub waiting_threads: WaitingThreads,

    /// The Label associated with this channel.
    ///
    /// This is set at channel creation time and does not change after that.
    ///
    /// See https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels
    pub label: oak_abi::label::Label,
}

impl std::fmt::Debug for Channel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Channel {{ #msgs={}, #readers={}, #writers={}, label={:?} }}",
            self.messages.read().unwrap().len(),
            self.readers.load(SeqCst),
            self.writers.load(SeqCst),
            self.label,
        )
    }
}
/// A reference to a [`Channel`]. Each [`Handle`] has an implicit direction such that it is only
/// possible to read or write to a [`Handle`] (exclusive or).
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Handle(pub oak_abi::Handle);

impl DotIdentifier for Handle {
    fn dot_id(&self) -> String {
        format!("h{}", self.0)
    }
}

/// The direction of a [`Handle`] can be discovered by querying the associated
/// [`Runtime`] [`Runtime::channel_get_direction`].
///
/// [`Runtime`]: crate::runtime::Runtime
/// [`Runtime::channel_get_direction`]: crate::runtime::Runtime::channel_get_direction
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum HandleDirection {
    Read,
    Write,
}

/// An internal identifier to track a [`Channel`]. This is implementation specific and should not
/// be visible outside the internals of [`Runtime`].
///
/// [`Runtime`]: crate::runtime::Runtime
type ChannelId = u64;

impl DotIdentifier for ChannelId {
    fn dot_id(&self) -> String {
        format!("channel{}", self)
    }
}

/// Ownership and mapping of [`Channel`]s to [`Handle`]s.
pub struct ChannelMapping {
    pub channels: RwLock<HashMap<ChannelId, Channel>>,

    pub next_channel_id: AtomicU64,

    pub readers: RwLock<HashMap<Handle, ChannelId>>,
    pub writers: RwLock<HashMap<Handle, ChannelId>>,
}

impl Channel {
    /// Create a new channel with the assumption there is currently one active reader and one active
    /// writer references.
    pub fn new(label: &oak_abi::label::Label) -> Channel {
        Channel {
            messages: RwLock::new(Messages::new()),
            writers: AtomicU64::new(1),
            readers: AtomicU64::new(1),
            waiting_threads: Mutex::new(HashMap::new()),
            label: label.clone(),
        }
    }

    /// Thread safe method that returns true when there is no longer at least one reader and one
    /// writer.
    pub fn is_orphan(&self) -> bool {
        self.readers.load(SeqCst) == 0 || self.writers.load(SeqCst) == 0
    }

    /// Thread safe method that returns true when there is no longer at least one reader or
    /// writer.
    pub fn has_no_reference(&self) -> bool {
        self.readers.load(SeqCst) == 0 && self.writers.load(SeqCst) == 0
    }

    /// Insert the given `thread` reference into `thread_id` slot of the HashMap of waiting
    /// channels attached to an underlying channel. This allows the channel to wake up any waiting
    /// channels by calling `thread::unpark` on all the threads it knows about.
    pub fn add_waiter(&self, thread_id: ThreadId, thread: &Arc<Thread>) {
        self.waiting_threads
            .lock()
            .unwrap()
            .insert(thread_id, Arc::downgrade(thread));
    }

    /// Decrement the [`Channel`] writer counter.
    pub fn dec_writer_count(&self) {
        if self.writers.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Writer count was already 0, something is very wrong!")
        }
    }

    /// Decrement the [`Channel`] reader counter.
    pub fn dec_reader_count(&self) {
        if self.readers.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Reader count was already 0, something is very wrong!")
        }
    }

    /// Increment the [`Channel`] writer counter.
    pub fn inc_writer_count(&self) -> u64 {
        self.writers.fetch_add(1, SeqCst)
    }

    /// Increment the [`Channel`] reader counter.
    pub fn inc_reader_count(&self) -> u64 {
        self.readers.fetch_add(1, SeqCst)
    }
}

impl ChannelMapping {
    /// Create a new empty [`ChannelMapping`].
    pub fn new() -> ChannelMapping {
        ChannelMapping {
            channels: RwLock::new(HashMap::new()),

            next_channel_id: AtomicU64::new(0),

            readers: RwLock::new(HashMap::new()),
            writers: RwLock::new(HashMap::new()),
        }
    }

    /// Creates a new [`Channel`] and returns a `(writer handle, reader handle)` pair.
    pub fn new_channel(&self, label: &oak_abi::label::Label) -> (Handle, Handle) {
        let channel_id = self.next_channel_id.fetch_add(1, SeqCst);
        self.channels
            .write()
            .unwrap()
            .insert(channel_id, Channel::new(label));
        (self.new_writer(channel_id), self.new_reader(channel_id))
    }

    /// Get a new free random [`Handle`] that is not used by any readers or writers.
    fn new_reference(&self) -> Handle {
        loop {
            let handle = Handle(rand::thread_rng().next_u64());

            let exists_reader = self.readers.read().unwrap().get(&handle).is_some();
            let exists_writer = self.writers.read().unwrap().get(&handle).is_some();

            if exists_reader || exists_writer {
                continue;
            }

            return handle;
        }
    }

    /// Create a new writer reference.
    fn new_writer(&self, channel_id: ChannelId) -> Handle {
        let reference = self.new_reference();
        self.writers.write().unwrap().insert(reference, channel_id);
        reference
    }

    /// Create a new reader reference.
    fn new_reader(&self, channel_id: ChannelId) -> Handle {
        let reference = self.new_reference();
        self.readers.write().unwrap().insert(reference, channel_id);
        reference
    }

    /// Attempt to retrieve the [`ChannelId`] associated with a reader [`Handle`].
    pub fn get_reader_channel(&self, reference: Handle) -> Result<ChannelId, OakStatus> {
        self.readers
            .read()
            .unwrap()
            .get(&reference)
            .map_or(Err(OakStatus::ErrBadHandle), |id| Ok(*id))
    }

    /// Attempt to retrieve the [`ChannelId`] associated with a writer [`Handle`].
    pub fn get_writer_channel(&self, reference: Handle) -> Result<ChannelId, OakStatus> {
        self.writers
            .read()
            .unwrap()
            .get(&reference)
            .map_or(Err(OakStatus::ErrBadHandle), |id| Ok(*id))
    }

    /// Perform an operation on a [`Channel`] associated with some [`ChannelId`].
    /// The channels read lock is held while the operation is performed.
    pub fn with_channel<U, F: FnOnce(&Channel) -> Result<U, OakStatus>>(
        &self,
        channel_id: ChannelId,
        f: F,
    ) -> Result<U, OakStatus> {
        let channels = self.channels.read().unwrap();
        let channel = channels.get(&channel_id).ok_or(OakStatus::ErrBadHandle)?;
        f(channel)
    }

    /// Deallocate a [`Handle`] reference. The reference will no longer be usable in
    /// operations, and the underlying [`Channel`] may become orphaned.
    pub fn remove_reference(&self, reference: Handle) -> Result<(), OakStatus> {
        if let Ok(channel_id) = self.get_writer_channel(reference) {
            {
                let mut channels = self.channels.write().unwrap();
                let channel = channels
                    .get(&channel_id)
                    .expect("remove_reference: Handle is invalid!");
                channel.dec_writer_count();
                if channel.has_no_reference() {
                    channels.remove(&channel_id);
                    debug!("remove_reference: deallocating channel {:?}", channel_id);
                }
            }

            self.writers.write().unwrap().remove(&reference);
        }

        if let Ok(channel_id) = self.get_reader_channel(reference) {
            {
                let mut channels = self.channels.write().unwrap();
                let channel = channels
                    .get(&channel_id)
                    .expect("remove_reference: Handle is invalid!");
                channel.dec_reader_count();
                if channel.has_no_reference() {
                    channels.remove(&channel_id);
                    debug!("remove_reference: deallocating channel {:?}", channel_id);
                }
            }

            self.readers.write().unwrap().remove(&reference);
        }

        Ok(())
    }

    /// Duplicate a [`Handle`] reference. This new reference and when it is closed will be
    /// tracked separately from the first [`Handle`]. For instance this is used by the
    /// [`Runtime`] to encode [`Channel`]s in messages.
    ///
    /// [`Runtime`]: crate::runtime::Runtime
    pub fn duplicate_reference(&self, reference: Handle) -> Result<Handle, OakStatus> {
        if let Ok(channel_id) = self.get_writer_channel(reference) {
            self.with_channel(channel_id, |channel| Ok(channel.inc_writer_count()))?;

            return Ok(self.new_writer(channel_id));
        }

        if let Ok(channel_id) = self.get_reader_channel(reference) {
            self.with_channel(channel_id, |channel| Ok(channel.inc_reader_count()))?;

            return Ok(self.new_reader(channel_id));
        }

        Err(OakStatus::ErrBadHandle)
    }

    /// Build a Dot nodes stanza for the `ChannelMapping`.
    #[cfg(feature = "oak_debug")]
    pub fn graph_nodes(&self) -> String {
        let mut s = String::new();
        writeln!(&mut s, "  {{").unwrap();
        writeln!(
            &mut s,
            "    node [shape=hexagon style=filled fillcolor=yellow]"
        )
        .unwrap();

        {
            for half_id in self.writers.read().unwrap().keys() {
                writeln!(&mut s, "    {}", half_id.dot_id()).unwrap();
            }
        }
        {
            for half_id in self.readers.read().unwrap().keys() {
                writeln!(&mut s, "    {}", half_id.dot_id()).unwrap();
            }
        }
        writeln!(&mut s, "  }}").unwrap();

        // Graph nodes for Channels.
        {
            writeln!(&mut s, "  {{").unwrap();
            writeln!(
                &mut s,
                "    node [shape=ellipse style=filled fillcolor=green]"
            )
            .unwrap();
            let channels = self.channels.read().unwrap();
            for channel_id in channels.keys().sorted() {
                let channel = channels.get(&channel_id).unwrap();
                writeln!(
                    &mut s,
                    "    {} [label=\"channel-{}\\nm={}, w={}, r={}\"]",
                    channel_id.dot_id(),
                    channel_id,
                    channel.messages.read().unwrap().len(),
                    channel.readers.load(SeqCst),
                    channel.writers.load(SeqCst),
                )
                .unwrap();
            }
            writeln!(&mut s, "  }}").unwrap();
        }
        s
    }

    /// Build a Dot edges stanza for the `ChannelMapping`, allowing for the set
    /// of nodes that have been already observed in the graph.
    #[cfg(feature = "oak_debug")]
    pub fn graph_edges(&self, seen: HashSet<Handle>) -> String {
        let mut s = String::new();
        {
            for (half_id, channel_id) in self.writers.read().unwrap().iter() {
                write!(&mut s, "  {} -> {}", half_id.dot_id(), channel_id.dot_id()).unwrap();
                if !seen.contains(half_id) {
                    error!("reader {:?} is not referenced by any node!", half_id);
                    write!(&mut s, "  [color=red style=bold]").unwrap();
                }
                writeln!(&mut s).unwrap();
            }
        }
        {
            for (half_id, channel_id) in self.readers.read().unwrap().iter() {
                write!(&mut s, "  {} -> {}", channel_id.dot_id(), half_id.dot_id()).unwrap();
                if !seen.contains(half_id) {
                    error!("writer {:?} is not referenced by any node!", half_id);
                    write!(&mut s, "  [color=red style=bold]").unwrap();
                }
                writeln!(&mut s).unwrap();
            }
        }
        s
    }

    #[cfg(feature = "oak_debug")]
    pub fn html_for_channel(&self, id: u64) -> Option<String> {
        let channel_id: ChannelId = id;
        Some(format!("placeholder for {}", channel_id))
    }

    #[cfg(feature = "oak_debug")]
    pub fn html_for_half(&self, id: u64) -> Option<String> {
        let half = Handle(id);
        Some(format!("placeholder for {:?}", half))
    }
}
