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

use std::collections::{HashMap, VecDeque};
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::SeqCst;
use std::sync::{Arc, Mutex, RwLock, Weak};
use std::thread::{Thread, ThreadId};

use log::debug;
use rand::RngCore;

use oak_abi::OakStatus;

use crate::Message;

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
#[derive(Debug)]
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

/// A reference to a [`Channel`]. Each [`Handle`] has an implicit direction such that it is only
/// possible to read or write to a [`Handle`] (exclusive or).
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Handle(oak_abi::Handle);

/// The direction of a [`Handle`] can be discovered by querying the associated
/// [`oak_runtime::Runtime`] [`oak_runtime::Runtime::channel_get_direction`].
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum HandleDirection {
    Read,
    Write,
}

/// An internal identifier to track a [`Channel`]. This is implementation specific and should not
/// be visible outside the internals of [`Runtime`].
type ChannelId = u64;

/// Ownership and mapping of [`Channel`]s to [`Handle`]s.
#[derive(Debug)]
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
    /// [`oak_runtime::Runtime`] to encode [`Channel`]s in messages.
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
}
