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

use oak_abi::{OakStatus};

use crate::platform;
use crate::{Message};

type Messages = VecDeque<Message>;

/// We use a `HashMap` keyed by `ThreadId` to prevent build up of stale `Weak<Thread>`s.
///
/// That is: If a thread waiting/blocked on a channel is woken by a different channel, its
/// `Weak<Thread>` will remain in the first channel's waiting_thread member. If a thread keeps
/// waiting on this first channel, and keeps being woken by other channels, it will keep re-adding
/// itself. We use a `HashMap` and insert at the current `ThreadId` so that we replace any stale
/// `Weak<Thread>`s which will have gone out of scope. (`wait_on_channels` drops the underlying arc
/// as soon as it is resumed.)
type WaitingThreads =
    platform::Mutex<HashMap<platform::thread::ThreadId, Weak<platform::thread::Thread>>>;

/// The internal implementation of a channel representation backed by a `VecDeque<Message>`.
/// Readers and writers to this channel must increment the reader/writer count. This is implemented
/// for `ChannelWriter`/`ChannelReader`, which will increment/decrement readers/writers when
/// cloning/dropping.
pub struct Channel {
    messages: platform::RwLock<Messages>,

    /// A HashMap of `ThreadId`s to `Weak<Thread>`s. This allows threads to insert a weak reference
    /// to themselves to be woken when a new message is available. Weak references are used so that
    /// if the thread is woken by a different channel, it can deallocate the underlying `Arc`
    /// instead of removing itself from all the `Channel`s it subscribed to.
    /// Threads can be woken up spuriously without issue.
    waiting_threads: WaitingThreads,
}


/// A helper type to determine if `try_read_message` was called with not enough `bytes_capacity`
/// and/or `handles_capacity`.
pub enum ReadStatus {
    Success(Message),
    NeedsCapacity(usize, usize),
}

impl Channel {
    pub fn new() -> Channel {
        Channel {
            messages: platform::RwLock::new(VecDeque::new()),
            waiting_threads: platform::Mutex::new(HashMap::new()),
        }
    }

    /// Write a message to a channel. Fails with `OakStatus::ERR_CHANNEL_CLOSED` if the underlying
    /// channel has been orphaned.
    pub fn write(&self, msg: Message) -> () {
        {
            let mut messages = self.messages.write().unwrap();

            messages.push_back(msg);
        }

        let mut waiting_threads = self.waiting_threads.lock().unwrap();

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
    }

    /// Thread safe. Read a message from a channel. Fails with `OakStatus::ERR_CHANNEL_CLOSED` if
    /// the underlying channel is empty and has been orphaned.
    pub fn read(&self) -> Option<Message> {
        let mut messages = self.messages.write().unwrap();
        messages.pop_front()
    }

    /// Thread safe. This function will return:
    /// - `READ_READY` if there is at least one message in the channel.
    /// - `ORPHANED` if there are no messages and there are no writers
    /// - `NOT_READ` if there are no messages but there are some writers
    pub fn status(&self) -> bool {
        let messages = self.messages.read().unwrap();
        messages.front().is_some()
    }

    /// Thread safe. Reads a message from the channel if `bytes_capacity` and `handles_capacity` are
    /// large enough to accept the message. Fails with `OakStatus::ERR_CHANNEL_CLOSED` if the
    /// underlying channel has been orphaned _and_ is empty. If there was not enough
    /// `bytes_capacity` or `handles_capacity`, `try_read_message` will return
    /// `Some(ReadStatus::NeedsCapacity(needed_bytes_capacity,needed_handles_capacity))`. Does not
    /// guarantee that the next call will succeed after capacity adjustments as another thread may
    /// have read the original message.
    pub fn try_read_message(
        &self,
        bytes_capacity: usize,
        handles_capacity: usize,
        is_orphan: bool,
    ) -> Result<Option<ReadStatus>, OakStatus> {
        let mut messages = self.messages.write().unwrap();
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
                        ReadStatus::Success(messages.pop_front().expect(
                            "Front element disappeared while we were holding the write lock!",
                        ))
                    },
                ))
            }
            None => {
                if is_orphan {
                    Err(OakStatus::ERR_CHANNEL_CLOSED)
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Insert the given `thread` reference into `thread_id` slot of the HashMap of waiting
    /// channels attached to an underlying channel. This allows the channel to wake up any waiting
    /// channels by calling `thread::unpark` on all the threads it knows about.
    pub fn add_waiter(
        &self,
        thread: &Arc<platform::thread::Thread>,
    ) {
        let thread_id = platform::thread::current().id();
        let mut waiting_threads = self.waiting_threads.lock().unwrap();
        waiting_threads.insert(thread_id, Arc::downgrade(thread));
    }
}
