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

use std::prelude::v1::*;

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Weak};

use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering::SeqCst;

use oak_platform::{Mutex, RwLock, Thread, ThreadId};

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
pub struct Channel {
    readers: AtomicUsize,
    writers: AtomicUsize,

    pub messages: RwLock<Messages>,

    /// A HashMap of `ThreadId`s to `Weak<Thread>`s. This allows threads to insert a weak reference
    /// to themselves to be woken when a new message is available. Weak references are used so that
    /// if the thread is woken by a different channel, it can deallocate the underlying `Arc`
    /// instead of removing itself from all the `Channel`s it subscribed to.
    /// Threads can be woken up spuriously without issue.
    pub waiting_threads: WaitingThreads,
}


/// Reference to a `Channel` that is `Clone`able and can be passed across threads. Channels are
/// multi-writer mult-reader.
#[derive(Clone)]
struct ChannelRef(Arc<Channel>);

/// Writer end to a `Channel`. `ChannelWriter` implements `Clone` and `Drop` to automatically
/// update the underlying channel.
pub struct ChannelWriter(ChannelRef);
/// Reader end to a `Channel`. `ChannelReader` implements `Clone` and `Drop` to automatically
/// update the underlying channel.
pub struct ChannelReader(ChannelRef);

/// A wrapper type to allow taking channel references without discriminating on direction. Used
/// when adding `ChannelRef`s into `Message`s.
#[derive(Clone)]
pub enum ChannelEither {
    Writer(ChannelWriter),
    Reader(ChannelReader),
}

impl Channel {
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
    fn remove_writer(&self) {
        if self.writers.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Writer count was already 0, something is very wrong!")
        }
    }

    /// Decrement the `Channel` reader counter.
    fn remove_reader(&self) {
        if self.readers.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Reader count was already 0, something is very wrong!")
        }
    }

    /// Increment the `Channel` writer counter.
    fn add_writer(&self) -> usize {
        self.writers.fetch_add(1, SeqCst)
    }

    /// Increment the `Channel` reader counter.
    fn add_reader(&self) -> usize {
        self.readers.fetch_add(1, SeqCst)
    }
}

/// Creates a new `ChannelWriter` and `ChannelReader` that reference the same underlying `Channel`.
pub fn new() -> (Arc<Channel>, ChannelWriter, ChannelReader) {
    let chan = Arc::new(Channel {
        readers: AtomicUsize::new(1),
        writers: AtomicUsize::new(1),
        messages: RwLock::new(VecDeque::new()),
        waiting_threads: Mutex::new(HashMap::new()),
    });
    let writer = ChannelWriter(ChannelRef::from_arc(chan.clone()));
    let reader = ChannelReader(ChannelRef::from_arc(chan.clone()));
    (chan, writer, reader)
}

impl ChannelRef {
    /// Internal method to take a thread-safe reference-counting pointer to a `Channel`.
    fn from_arc(arc: Arc<Channel>) -> ChannelRef {
        ChannelRef(arc)
    }
}

impl std::ops::Deref for ChannelRef {
    type Target = Channel;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::Deref for ChannelWriter {
    type Target = Channel;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Drop for ChannelWriter {
    fn drop(&mut self) {
        self.0.remove_writer();
    }
}

impl Clone for ChannelWriter {
    fn clone(&self) -> Self {
        self.0.add_writer();
        ChannelWriter(self.0.clone())
    }
}

/// A helper type to determine if `try_read_message` was called with not enough `bytes_capacity`
/// and/or `handles_capacity`.
pub enum ReadStatus {
    Success(Message),
    NeedsCapacity(usize, usize),
}

impl std::ops::Deref for ChannelReader {
    type Target = Channel;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Drop for ChannelReader {
    fn drop(&mut self) {
        self.0.remove_reader();
    }
}

impl Clone for ChannelReader {
    fn clone(&self) -> Self {
        self.0.add_reader();
        ChannelReader(self.0.clone())
    }
}
