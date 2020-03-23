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

use core::sync::atomic::Ordering::SeqCst;
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::AtomicU64;
use std::sync::{Arc, Mutex, RwLock, Weak};
use std::thread::{Thread, ThreadId};

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
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct ChannelRef(u64);

type ChannelId = u64;

#[derive(Debug)]
pub struct ChannelMapping {
    pub channels: RwLock<HashMap<ChannelId, Channel>>,

    pub next_channel: AtomicU64,

    pub readers: RwLock<HashMap<ChannelRef, ChannelId>>,
    pub writers: RwLock<HashMap<ChannelRef, ChannelId>>,

    pub next_reference: AtomicU64,
}

impl Channel {
    pub fn new() -> Channel {
        Channel {
            messages: RwLock::new(Messages::new()),
            writers: AtomicU64::new(1),
            readers: AtomicU64::new(1),
            waiting_threads: Mutex::new(HashMap::new()),
        }
    }

    /// Thread safe method that returns true when there is no longer at least one reader and one
    /// writer.
    pub fn is_orphan(&self) -> bool {
        self.readers.load(SeqCst) == 0 || self.writers.load(SeqCst) == 0
    }

    /// Insert the given `thread` reference into `thread_id` slot of the HashMap of waiting
    /// channels attached to an underlying channel. This allows the channel to wake up any waiting
    /// channels by calling `thread::unpark` on all the threads it knows about.
    pub fn add_waiter(&self, thread_id: ThreadId, thread: &Arc<Thread>) {
        let mut waiting_threads = self.waiting_threads.lock().unwrap();
        waiting_threads.insert(thread_id, Arc::downgrade(thread));
    }

    /// Decrement the `Channel` writer counter.
    pub fn remove_writer(&self) {
        if self.writers.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Writer count was already 0, something is very wrong!")
        }
    }

    /// Decrement the `Channel` reader counter.
    pub fn remove_reader(&self) {
        if self.readers.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Reader count was already 0, something is very wrong!")
        }
    }

    /// Increment the `Channel` writer counter.
    pub fn add_writer(&self) -> u64 {
        self.writers.fetch_add(1, SeqCst)
    }

    /// Increment the `Channel` reader counter.
    pub fn add_reader(&self) -> u64 {
        self.readers.fetch_add(1, SeqCst)
    }
}

impl ChannelMapping {
    pub fn new() -> ChannelMapping {
        ChannelMapping {
            channels: RwLock::new(HashMap::new()),

            next_channel: AtomicU64::new(0),

            readers: RwLock::new(HashMap::new()),
            writers: RwLock::new(HashMap::new()),

            next_reference: AtomicU64::new(0),
        }
    }

    fn new_channel(&self) -> ChannelId {
        let id = self.next_channel.fetch_add(1, SeqCst);
        let mut channels = self.channels.write().unwrap();
        channels.insert(id, Channel::new());
        id
    }

    fn new_reference(&self) -> ChannelRef {
        ChannelRef(self.next_reference.fetch_add(1, SeqCst))
    }

    fn new_writer(&self, channel: ChannelId) -> ChannelRef {
        let reference = self.new_reference();
        let mut writers = self.writers.write().unwrap();
        writers.insert(reference, channel);
        reference
    }

    fn new_reader(&self, channel: ChannelId) -> ChannelRef {
        let reference = self.new_reference();
        let mut readers = self.readers.write().unwrap();
        readers.insert(reference, channel);
        reference
    }

    pub fn make_channel(&self) -> (ChannelRef, ChannelRef) {
        let channel_id = self.new_channel();
        (self.new_writer(channel_id), self.new_reader(channel_id))
    }

    pub fn get_reader_channel(&self, reference: ChannelRef) -> Result<ChannelId, OakStatus> {
        let readers = self.readers.read().unwrap();
        readers
            .get(&reference)
            .map_or(Err(OakStatus::ErrBadHandle), |id| Ok(*id))
    }

    pub fn get_writer_channel(&self, reference: ChannelRef) -> Result<ChannelId, OakStatus> {
        let writers = self.writers.read().unwrap();
        writers
            .get(&reference)
            .map_or(Err(OakStatus::ErrBadHandle), |id| Ok(*id))
    }

    pub fn with_channel<U, F: FnOnce(&Channel) -> Result<U, OakStatus>>(
        &self,
        channel_id: ChannelId,
        f: F,
    ) -> Result<U, OakStatus> {
        let channels = self.channels.read().unwrap();
        let channel = channels.get(&channel_id).ok_or(OakStatus::ErrBadHandle)?;
        f(channel)
    }

    pub fn remove_reference(&self, reference: ChannelRef) -> Result<(), OakStatus> {
        if let Ok(channel_id) = self.get_writer_channel(reference) {
            self.with_channel(channel_id, |channel| {
                channel.remove_writer();
                Ok(())
            })?;

            let mut writers = self.writers.write().unwrap();
            writers.remove(&reference);
        }

        if let Ok(channel_id) = self.get_reader_channel(reference) {
            self.with_channel(channel_id, |channel| {
                channel.remove_reader();
                Ok(())
            })?;

            let mut readers = self.readers.write().unwrap();
            readers.remove(&reference);
        }

        Ok(())
    }

    pub fn duplicate_reference(&self, reference: ChannelRef) -> Result<ChannelRef, OakStatus> {
        if let Ok(channel_id) = self.get_writer_channel(reference) {
            self.with_channel(channel_id, |channel| Ok(channel.add_writer()))?;

            return Ok(self.new_writer(channel_id));
        }

        if let Ok(channel_id) = self.get_reader_channel(reference) {
            self.with_channel(channel_id, |channel| Ok(channel.add_reader()))?;

            return Ok(self.new_reader(channel_id));
        }

        Err(OakStatus::ErrBadHandle)
    }
}
