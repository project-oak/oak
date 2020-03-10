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

use std::collections::HashMap;
use std::string::String;
use std::sync::{Arc, Weak};

use core::sync::atomic::Ordering::SeqCst;
use core::sync::atomic::{AtomicBool, AtomicU64};

use oak_abi::{ChannelReadStatus, OakStatus};
use oak_platform::{JoinHandle, Mutex};

use log::debug;
use rand::RngCore;

use crate::message::Message;
use crate::node;

mod channel;
pub use channel::{ChannelEither, ChannelReader, ChannelWriter, ReadStatus};

type Channels = Vec<Weak<channel::Channel>>;

#[derive(Debug)]
struct Node {
    reference: NodeRef,
    join_handle: Option<JoinHandle>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct NodeRef(u64);

pub struct Configuration {
    pub nodes: HashMap<String, node::Configuration>,
    pub entry_module: String,
    pub entrypoint: String,
}

/// Runtime structure for configuring and running a set of Oak nodes.
pub struct Runtime {
    configurations: HashMap<String, node::Configuration>,
    terminating: AtomicBool,
    channels: Mutex<Channels>,
    nodes: Mutex<HashMap<NodeRef, Node>>,
    next_node: AtomicU64,
}

impl Runtime {
    /// Configure and run the protobuf specified `ApplicationConfiguration`. After creating a
    /// `Runtime` calling `stop` will send termination signals to nodes and wait for them to
    /// terminate.
    pub fn configure_and_run(
        config: Configuration,
    ) -> Result<(RuntimeRef, ChannelWriter), OakStatus> {
        let runtime = Runtime {
            configurations: config.nodes,
            terminating: AtomicBool::new(false),
            channels: Mutex::new(Vec::new()),
            nodes: Mutex::new(HashMap::new()),
            next_node: AtomicU64::new(0),
        };

        let runtime = RuntimeRef(Arc::new(runtime));

        let (chan_writer, chan_reader) = runtime.new_channel();

        runtime.node_create(&config.entry_module, &config.entrypoint, chan_reader)?;

        Ok((runtime, chan_writer))
    }

    /// Thread safe method for determining if the `Runtime` is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Thread safe method for signaling termination to a `Runtime` and waiting for its node
    /// threads to terminate.
    pub fn stop(&self) {
        let mut threads = {
            let mut nodes = self.nodes.lock().unwrap();
            self.terminating.store(true, SeqCst);

            std::mem::replace(&mut *nodes, HashMap::new())
        };

        // Unpark any threads that are blocked waiting on channels.
        for thread in threads.values() {
            thread.join_handle.as_ref().unwrap().thread().unpark();
        }

        for (_, thread) in threads.drain() {
            thread
                .join_handle
                .unwrap()
                .join()
                .expect("Failed to join handle");
        }
    }

    /// Creates a new channel.
    pub fn new_channel(&self) -> (ChannelWriter, ChannelReader) {
        let (c, w, r) = channel::new();
        let mut channels = self.channels.lock().unwrap();
        channels.push(Arc::downgrade(&c));
        (w, r)
    }

    /// Reads the statuses from a slice of `Option<&ChannelReader>`s.
    /// [`ChannelReadStatus::InvalidChannel`] is set for `None` readers in the slice. For `Some(_)`
    /// readers, the result is set from a call to `has_message`.
    fn readers_statuses(&self, readers: &[Option<&ChannelReader>]) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|chan| {
                chan.map_or(ChannelReadStatus::InvalidChannel, |chan| {
                    self.channel_status(chan)
                })
            })
            .collect()
    }

    /// Waits on a slice of `Option<&ChannelReader>`s, blocking until one of the following
    /// conditions:
    /// - If the `Runtime` is terminating this will return immediately with an `ErrTerminated`
    ///   status for each channel.
    /// - If all readers are in an erroneous status, e.g. when all `ChannelReaders` are orphaned,
    ///   this will immediately return the channels statuses.
    /// - If any of the channels is able to read a message, the corresponding element in the
    ///   returned vector will be set to `Ok(ReadReady)`, with `Ok(NotReady)` signaling the channel
    ///   has no message available
    ///
    /// In particular, if there is at least one channel in good status and no messages on said
    /// channel available, `wait_on_channels` will continue to block until a message is
    /// available.
    pub fn wait_on_channels(
        &self,
        readers: &[Option<&ChannelReader>],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        let thread = oak_platform::current_thread();
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

            let thread_id = oak_platform::current_thread().id();
            let thread_ref = Arc::new(thread.clone());

            for reader in readers {
                if let Some(reader) = reader {
                    reader.add_waiter(thread_id, &thread_ref);
                }
            }
            let statuses = self.readers_statuses(readers);

            let all_unreadable = statuses.iter().all(|&s| {
                s == ChannelReadStatus::InvalidChannel || s == ChannelReadStatus::Orphaned
            });
            let any_ready = statuses.iter().any(|&s| s == ChannelReadStatus::ReadReady);

            if all_unreadable || any_ready {
                return Ok(statuses);
            }

            debug!(
                "wait_on_channels: channels not ready, parking thread {:?}",
                oak_platform::current_thread().id()
            );

            oak_platform::park_thread();

            debug!(
                "wait_on_channels: thread {:?} re-woken",
                oak_platform::current_thread().id()
            );
        }
        Err(OakStatus::ErrTerminated)
    }

    /// Write a message to a channel. Fails with [`OakStatus::ErrChannelClosed`] if the underlying
    /// channel has been orphaned.
    pub fn channel_write(&self, channel: &ChannelWriter, msg: Message) -> Result<(), OakStatus> {
        if channel.is_orphan() {
            return Err(OakStatus::ErrChannelClosed);
        }

        {
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
    }

    /// Thread safe. Read a message from a channel. Fails with [`OakStatus::ErrChannelClosed`] if
    /// the underlying channel is empty and has been orphaned.
    pub fn channel_read(&self, channel: &ChannelReader) -> Result<Option<Message>, OakStatus> {
        let mut messages = channel.messages.write().unwrap();
        match messages.pop_front() {
            Some(m) => Ok(Some(m)),
            None => {
                if channel.is_orphan() {
                    Err(OakStatus::ErrChannelClosed)
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Thread safe. This function returns:
    /// - [`ChannelReadStatus::ReadReady`] if there is at least one message in the channel.
    /// - [`ChannelReadStatus::Orphaned`] if there are no messages and there are no writers
    /// - [`ChannelReadStatus::NotReady`] if there are no messages but there are some writers
    pub fn channel_status(&self, channel: &ChannelReader) -> ChannelReadStatus {
        let messages = channel.messages.read().unwrap();
        if messages.front().is_some() {
            ChannelReadStatus::ReadReady
        } else if channel.is_orphan() {
            ChannelReadStatus::Orphaned
        } else {
            ChannelReadStatus::NotReady
        }
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
        channel: &ChannelReader,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<ReadStatus>, OakStatus> {
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
                        ReadStatus::Success(messages.pop_front().expect(
                            "Front element disappeared while we were holding the write lock!",
                        ))
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
    }
}

/// A reference to a `Runtime`
#[derive(Clone)]
pub struct RuntimeRef(Arc<Runtime>);

impl RuntimeRef {
    /// Thread safe method that attempts to create a node within the `Runtime` corresponding to a
    /// given module name and entrypoint. The `reader: ChannelReader` is passed to the newly
    /// created node.
    ///
    /// `node_create` is a method of `RuntimeRef` and not `Runtime`, so that the underlying
    /// `Arc<Runtime>` can be passed to `conf.new_instance` and given to a new node thread.
    pub fn node_create(
        &self,
        module_name: &str,
        entrypoint: &str,
        reader: ChannelReader,
    ) -> Result<(), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        let reference = NodeRef(self.next_node.fetch_add(1, SeqCst));
        let mut nodes = self.nodes.lock().unwrap();

        match self
            .configurations
            .get(module_name)
            .ok_or(OakStatus::ErrInvalidArgs)
            .and_then(|conf| {
                conf.new_instance(
                    module_name,
                    self.clone(),
                    reference,
                    entrypoint.to_owned(),
                    reader,
                )
            }) {
            Ok(join_handle) => {
                nodes.get_mut(&reference).unwrap().join_handle = Some(join_handle);
            }
            Err(e) => {
                nodes.remove(&reference);
                return Err(e);
            }
        }

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
