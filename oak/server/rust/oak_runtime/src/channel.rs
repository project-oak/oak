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

use std::collections::VecDeque;
use std::sync::Arc;
use std::vec::Vec;

use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering::SeqCst;

use oak_abi::OakStatus;

use crate::platform;
use crate::{Message, RuntimeRef};

type Messages = VecDeque<Message>;

/// The internal implementation of a channel representation backed by a `VecDeque<Message>`.
/// Readers and writers to this channel must increment the reader/writer count. This is implemented
/// for `ChannelWriter`/`ChannelReader`, which will increment/decrement readers/writers when
/// cloning/dropping.
pub struct Channel {
    readers: AtomicUsize,
    writers: AtomicUsize,
    messages: platform::RwLock<Messages>,
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
    fn is_orphan(&self) -> bool {
        self.readers.load(SeqCst) == 0 || self.writers.load(SeqCst) == 0
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
pub fn new() -> (ChannelWriter, ChannelReader) {
    let chan = Arc::new(Channel {
        readers: AtomicUsize::new(1),
        writers: AtomicUsize::new(1),
        messages: platform::RwLock::new(VecDeque::new()),
    });
    let writer = ChannelWriter(ChannelRef::from_arc(chan.clone()));
    let reader = ChannelReader(ChannelRef::from_arc(chan.clone()));
    (writer, reader)
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

impl ChannelWriter {
    /// Write a message to a channel. Fails with `OakStatus::ERR_CHANNEL_CLOSED` if the underlying
    /// channel has been orphaned.
    pub fn write(&self, msg: Message) -> Result<(), OakStatus> {
        if self.is_orphan() {
            return Err(OakStatus::ERR_CHANNEL_CLOSED);
        }
        let mut messages = self.messages.write().unwrap();
        messages.push_back(msg);
        Ok(())
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

impl ChannelReader {
    /// Thread safe. Read a message from a channel. Fails with `OakStatus::ERR_CHANNEL_CLOSED` if
    /// the underlying channel is empty and has been orphaned.
    pub fn read(&self) -> Result<Option<Message>, OakStatus> {
        let mut messages = self.messages.write().unwrap();
        match messages.pop_front() {
            Some(m) => Ok(Some(m)),
            None => {
                if self.is_orphan() {
                    Err(OakStatus::ERR_CHANNEL_CLOSED)
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Thread safe. Returns `Ok(true)` if there is at least one message in the channel. Fails with
    /// `OakStatus::ERR_CHANNEL_CLOSED` if the underlying channel has been orphaned _and_ is empty.
    // TODO(#566)
    pub fn has_message(&self) -> Result<bool, OakStatus> {
        let messages = self.messages.read().unwrap();
        if messages.front().is_some() {
            Ok(true)
        } else if self.is_orphan() {
            Err(OakStatus::ERR_CHANNEL_CLOSED)
        } else {
            Ok(false)
        }
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
                if self.is_orphan() {
                    Err(OakStatus::ERR_CHANNEL_CLOSED)
                } else {
                    Ok(None)
                }
            }
        }
    }
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

/// Reads the statuses from a slice of `Option<&ChannelReader>`s.
/// `Err(OakStatus::ERR_INVALID_ARGS)` is set for `None` readers in the slice. For `Some(_)`
/// readers, the corresponding `Result` is set from a call to `has_message`.
pub fn readers_statuses(readers: &[Option<&ChannelReader>]) -> Vec<Result<bool, OakStatus>> {
    readers
        .iter()
        .map(|chan| chan.map_or(Err(OakStatus::ERR_INVALID_ARGS), |chan| chan.has_message()))
        .collect()
}

/// Waits on a slice of `Option<&ChannelReader>`s, blocking until one of the following conditions:
/// - If the `Runtime` is terminating this will return immediately with an `ERR_TERMINATED` status
///   for each channel.
/// - If all readers are in an erroneous status, e.g. when all `ChannelReaders` are orphaned, this
///   will immediately return the channels statuses.
/// - If any of the channels is able to read a message, the corresponding element in the returned
///   vector will be set to `Ok(true)`, with `Ok(false)` signaling the channel has no message
///   available
///
/// In particular, if there is at least one channel in good status and no messages on said channel
/// available, `wait_on_channels` will continue to block until a message is available.
pub fn wait_on_channels(
    runtime: &RuntimeRef,
    readers: &[Option<&ChannelReader>],
) -> Vec<Result<bool, OakStatus>> {
    while !runtime.is_terminating() {
        let statuses = readers_statuses(readers);

        if statuses.iter().all(|s| s.is_err()) || statuses.iter().any(|s| s.unwrap_or(false)) {
            return statuses;
        }

        crate::yield_thread();
    }
    vec![Err(OakStatus::ERR_TERMINATED); readers.len()]
}
