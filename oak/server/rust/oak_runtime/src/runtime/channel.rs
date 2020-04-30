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

use crate::{message::Message, runtime::DotIdentifier};
use log::debug;
use oak_abi::OakStatus;
use std::{
    collections::{HashMap, VecDeque},
    sync::{
        atomic::{AtomicU64, Ordering::SeqCst},
        Arc, Mutex, RwLock, RwLockReadGuard, Weak,
    },
    thread::{Thread, ThreadId},
};

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
///
/// Channels are reference counted using `Arc<Channel>`, which are always in the form of a
/// `ChannelHalf` object that references one end of the `Channel` (read or write) and which
/// is included in the `reader_count` or `writer_count`.
pub struct Channel {
    // An internal identifier for this channel. Purely for disambiguation in debugging output.
    id: ChannelId,

    pub messages: RwLock<Messages>,

    // Counts of the numbers of `ChannelHalf` objects that refer to this channel.
    writer_count: AtomicU64,
    reader_count: AtomicU64,

    /// A HashMap of `ThreadId`s to `Weak<Thread>`s. This allows threads to insert a weak reference
    /// to themselves to be woken when a new message is available. Weak references are used so that
    /// if the thread is woken by a different channel, it can deallocate the underlying `Arc`
    /// instead of removing itself from all the `Channel`s it subscribed to.
    /// Threads can be woken up spuriously without issue.
    waiting_threads: WaitingThreads,

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
            "Channel {{ id={}, #readers={}, #writers={}, label={:?} }}",
            self.id,
            self.reader_count.load(SeqCst),
            self.writer_count.load(SeqCst),
            self.label,
        )
    }
}

/// A reference to one half of a [`Channel`].
pub struct ChannelHalf {
    channel: Arc<Channel>,
    pub direction: ChannelHalfDirection,
}

impl ChannelHalf {
    // Constructor for `ChannelHalf` keeps the underlying channel's reader/writer count
    // up-to-date.
    pub fn new(channel: Arc<Channel>, direction: ChannelHalfDirection) -> Self {
        match direction {
            ChannelHalfDirection::Write => channel.inc_writer_count(),
            ChannelHalfDirection::Read => channel.inc_reader_count(),
        };
        ChannelHalf { channel, direction }
    }

    // Get read-only access to the channel's messages.  For debugging/introspection
    // purposes.
    pub fn get_messages(&self) -> RwLockReadGuard<Messages> {
        self.channel.messages.read().unwrap()
    }

    // Wake any threads waiting on the underlying channel.
    pub fn wake_waiters(&self) {
        self.channel.wake_waiters();
    }
}

// Manual implementation of the `Clone` trait to keep the counts for the underlying channel in sync.
impl Clone for ChannelHalf {
    fn clone(&self) -> Self {
        ChannelHalf::new(self.channel.clone(), self.direction)
    }
}

// Manual implementation of the `Drop` trait to keep the counts for the underlying channel in sync.
impl Drop for ChannelHalf {
    fn drop(&mut self) {
        match self.direction {
            ChannelHalfDirection::Write => self.channel.dec_writer_count(),
            ChannelHalfDirection::Read => self.channel.dec_reader_count(),
        };
        if self.direction == ChannelHalfDirection::Write && !self.channel.has_writers() {
            // This was the last writer to the channel: wake any waiters so they
            // can be aware that the channel is orphaned.
            debug!(
                "last writer for channel {} gone, wake waiters",
                self.channel.id
            );
            self.wake_waiters();
        }
    }
}

impl std::fmt::Debug for ChannelHalf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Channel {} {}",
            self.channel.id,
            match self.direction {
                ChannelHalfDirection::Write => "WRITE",
                ChannelHalfDirection::Read => "READ",
            },
        )
    }
}

impl DotIdentifier for ChannelHalf {
    fn dot_id(&self) -> String {
        self.channel.id.dot_id()
    }
}

/// Perform an operation on a [`Channel`] associated with a [`ChannelId`].
fn with_channel<U, F: FnOnce(Arc<Channel>) -> Result<U, OakStatus>>(
    half: &ChannelHalf,
    f: F,
) -> Result<U, OakStatus> {
    f(half.channel.clone())
}

/// Perform an operation on a [`Channel`] associated with a reader [`ChannelHalf`].
pub fn with_reader_channel<U, F: FnOnce(Arc<Channel>) -> Result<U, OakStatus>>(
    half: &ChannelHalf,
    f: F,
) -> Result<U, OakStatus> {
    if half.direction != ChannelHalfDirection::Read {
        return Err(OakStatus::ErrBadHandle);
    }
    with_channel(half, f)
}

/// Perform an operation on a [`Channel`] associated with a writer [`ChannelHalf`].
pub fn with_writer_channel<U, F: FnOnce(Arc<Channel>) -> Result<U, OakStatus>>(
    half: &ChannelHalf,
    f: F,
) -> Result<U, OakStatus> {
    if half.direction != ChannelHalfDirection::Write {
        return Err(OakStatus::ErrBadHandle);
    }
    with_channel(half, f)
}

/// The direction of a [`ChannelHalf`].
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum ChannelHalfDirection {
    Read,
    Write,
}

/// An internal identifier to track a [`Channel`].
type ChannelId = u64;

impl DotIdentifier for ChannelId {
    fn dot_id(&self) -> String {
        format!("channel{}", self)
    }
}

impl Drop for Channel {
    fn drop(&mut self) {
        debug!("dropping Channel object {:?}", self);
        // There should be no waiters for this channel (a waiting Node would have
        // to have a `Handle` to wait on, which would be a reference that pins this
        // channel to existence) so no need to `wake_waiters()`.
        // Deliberately clear the HashMap under the lock to avoid a TSAN report.
        self.waiting_threads.lock().unwrap().clear();
    }
}

impl Channel {
    pub fn new(id: ChannelId, label: &oak_abi::label::Label) -> Arc<Channel> {
        debug!("create new Channel object with ID {}", id);
        Arc::new(Channel {
            id,
            messages: RwLock::new(Messages::new()),
            writer_count: AtomicU64::new(0),
            reader_count: AtomicU64::new(0),
            waiting_threads: Mutex::new(HashMap::new()),
            label: label.clone(),
        })
    }

    /// Determine whether there are any readers of the channel.
    pub fn has_readers(&self) -> bool {
        self.reader_count.load(SeqCst) > 0
    }

    /// Determine whether there are any writers of the channel.
    pub fn has_writers(&self) -> bool {
        self.writer_count.load(SeqCst) > 0
    }

    /// Determine whether there are any users of the channel.
    pub fn has_users(&self) -> bool {
        self.has_readers() || self.has_writers()
    }

    /// Decrement the [`Channel`] writer counter.
    fn dec_writer_count(&self) {
        if self.writer_count.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Writer count was already 0, something is very wrong!")
        }
    }

    /// Decrement the [`Channel`] reader counter.
    fn dec_reader_count(&self) {
        if self.reader_count.fetch_sub(1, SeqCst) == 0 {
            panic!("remove_reader: Reader count was already 0, something is very wrong!")
        }
    }

    /// Increment the [`Channel`] writer counter.
    fn inc_writer_count(&self) -> u64 {
        self.writer_count.fetch_add(1, SeqCst)
    }

    /// Increment the [`Channel`] reader counter.
    fn inc_reader_count(&self) -> u64 {
        self.reader_count.fetch_add(1, SeqCst)
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

    pub fn wake_waiters(&self) {
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
        let mut waiting_threads = self.waiting_threads.lock().unwrap();
        for thread in waiting_threads.values() {
            if let Some(thread) = thread.upgrade() {
                thread.unpark();
            }
        }
        waiting_threads.clear();
    }
}
