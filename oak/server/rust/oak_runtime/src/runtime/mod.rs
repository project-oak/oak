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

use std::collections::HashMap;
use std::string::String;
use std::sync::{Arc, Mutex};
use std::{thread, thread::JoinHandle};

use core::sync::atomic::Ordering::SeqCst;
use core::sync::atomic::{AtomicBool, AtomicU64};

use oak_abi::{ChannelReadStatus, OakStatus};

use log::debug;

use crate::message::Message;
use crate::node;

mod channel;
pub use channel::{Handle, HandleDirection};

#[derive(Debug)]
struct Node {
    reference: NodeRef,
    join_handle: JoinHandle<()>,

    /// The Label associated with this node.
    ///
    /// This is set at node creation time and does not change after that.
    ///
    /// See https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels
    label: oak_abi::label::Label,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct NodeRef(u64);

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

/// Runtime structure for configuring and running a set of Oak nodes.
pub struct Runtime {
    configurations: HashMap<String, node::Configuration>,
    terminating: AtomicBool,

    channels: channel::ChannelMapping,

    nodes: Mutex<HashMap<NodeRef, Node>>,
    next_node_reference: AtomicU64,
}

impl Runtime {
    /// Configure and run the protobuf specified Application [`Configuration`]. After creating a
    /// [`Runtime`], calling [`Runtime::stop`] will send termination signals to nodes and wait for
    /// them to terminate. This returns a [`RuntimeRef`] reference to the created runtime, and a
    /// writeable [`Handle`] to send messages into the runtime. To receive messages, creating a new
    /// channel and passing the write [`Handle`] into the runtime will enable messages to be
    /// read back out.
    pub fn configure_and_run(config: Configuration) -> Result<(RuntimeRef, Handle), OakStatus> {
        let runtime = Runtime {
            configurations: config.nodes,
            terminating: AtomicBool::new(false),
            channels: channel::ChannelMapping::new(),
            nodes: Mutex::new(HashMap::new()),
            next_node_reference: AtomicU64::new(0),
        };

        let runtime = RuntimeRef(Arc::new(runtime));

        // When first starting, we assign the least privileged label to the channel connecting the
        // outside world to the entry point node.
        let (chan_writer, chan_reader) =
            runtime.new_channel(&oak_abi::label::Label::public_trusted());

        runtime.node_create(
            &config.entry_module,
            &config.entrypoint,
            // When first starting, we assign the least privileged label to the entry point node.
            &oak_abi::label::Label::public_trusted(),
            chan_reader,
        )?;

        runtime.channel_close(chan_reader)?;

        Ok((runtime, chan_writer))
    }

    /// Thread safe method for determining if the [`Runtime`] is terminating.
    pub fn is_terminating(&self) -> bool {
        self.terminating.load(SeqCst)
    }

    /// Thread safe method for signaling termination to a [`Runtime`] and waiting for its node
    /// threads to terminate.
    pub fn stop(&self) {
        // Take the list of nodes out of the runtime instance, and set the terminating flag; this
        // will prevent additional nodes from starting to wait again, because `wait_on_channels`
        // will return immediately with `OakStatus::ErrTerminated`.
        let mut nodes = {
            let mut nodes = self.nodes.lock().unwrap();
            self.terminating.store(true, SeqCst);

            std::mem::replace(&mut *nodes, HashMap::new())
        };

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

        // Wait for the main thread of each node to finish. Any thread that was blocked on
        // `wait_on_channels` is now unblocked and received `OakStatus::ErrTerminated`, so we wait
        // for any additional work to be finished here. This may take an arbitrary amount of time,
        // depending on the work that the node thread has to perform, but at least we know that the
        // it will not be able to enter again in a blocking state.
        for (_, node) in nodes.drain() {
            node.join_handle.join().expect("Failed to join handle");
        }
    }

    /// Creates a new channel.
    pub fn new_channel(&self, label: &oak_abi::label::Label) -> (Handle, Handle) {
        self.channels.new_channel(label)
    }

    /// Reads the statuses from a slice of `Option<&ChannelReader>`s.
    /// [`ChannelReadStatus::InvalidChannel`] is set for `None` readers in the slice. For `Some(_)`
    /// readers, the result is set from a call to `has_message`.
    fn readers_statuses(&self, readers: &[Option<Handle>]) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|chan| {
                chan.map_or(ChannelReadStatus::InvalidChannel, |chan| {
                    self.channel_status(chan)
                        .unwrap_or(ChannelReadStatus::InvalidChannel)
                })
            })
            .collect()
    }

    /// Waits on a slice of `Option<&ChannelReader>`s, blocking until one of the following
    /// conditions:
    /// - If the [`Runtime`] is terminating this will return immediately with an `ErrTerminated`
    ///   status for each channel.
    /// - If all readers are in an erroneous status, e.g. when all [`ChannelReader`]s are orphaned,
    ///   this will immediately return the channels statuses.
    /// - If any of the channels is able to read a message, the corresponding element in the
    ///   returned vector will be set to `Ok(ReadReady)`, with `Ok(NotReady)` signaling the channel
    ///   has no message available
    ///
    /// In particular, if there is at least one channel in good status and no messages on said
    /// channel available, [`Runtime::wait_on_channels`] will continue to block until a message is
    /// available.
    pub fn wait_on_channels(
        &self,
        readers: &[Option<Handle>],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
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

            let thread_id = thread.id();
            let thread_ref = Arc::new(thread.clone());

            for reader in readers {
                if let Some(reader) = reader {
                    self.channels.with_channel(
                        self.channels.get_reader_channel(*reader)?,
                        |channel| {
                            channel.add_waiter(thread_id, &thread_ref);
                            Ok(())
                        },
                    )?;
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
                thread::current()
            );

            thread::park();

            debug!("wait_on_channels: thread {:?} re-woken", thread::current());
        }
        Err(OakStatus::ErrTerminated)
    }

    /// Write a message to a channel. Fails with [`OakStatus::ErrChannelClosed`] if the underlying
    /// channel has been orphaned.
    pub fn channel_write(&self, reference: Handle, msg: Message) -> Result<(), OakStatus> {
        self.channels.with_channel(self.channels.get_writer_channel(reference)?, |channel|{

        if channel.is_orphan() {
            return Err(OakStatus::ErrChannelClosed);
        }

        {
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
        })
    }

    /// Thread safe. Read a message from a channel. Fails with [`OakStatus::ErrChannelClosed`] if
    /// the underlying channel is empty and has been orphaned.
    pub fn channel_read(&self, reference: Handle) -> Result<Option<Message>, OakStatus> {
        self.channels
            .with_channel(self.channels.get_reader_channel(reference)?, |channel| {
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
            })
    }

    /// Thread safe. This function returns:
    /// - [`ChannelReadStatus::ReadReady`] if there is at least one message in the channel.
    /// - [`ChannelReadStatus::Orphaned`] if there are no messages and there are no writers
    /// - [`ChannelReadStatus::NotReady`] if there are no messages but there are some writers
    pub fn channel_status(&self, reference: Handle) -> Result<ChannelReadStatus, OakStatus> {
        self.channels
            .with_channel(self.channels.get_reader_channel(reference)?, |channel| {
                let messages = channel.messages.read().unwrap();
                Ok(if messages.front().is_some() {
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
        reference: Handle,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<ReadStatus>, OakStatus> {
        self.channels
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
            })
    }

    /// Return the direction of a [`Handle`]. This is useful when reading
    /// [`Messages`] which contain [`Handle`]'s.
    pub fn channel_get_direction(&self, reference: Handle) -> Result<HandleDirection, OakStatus> {
        {
            let readers = self.channels.readers.read().unwrap();
            if readers.contains_key(&reference) {
                return Ok(HandleDirection::Read);
            }
        }
        {
            let writers = self.channels.writers.read().unwrap();
            if writers.contains_key(&reference) {
                return Ok(HandleDirection::Write);
            }
        }
        Err(OakStatus::ErrBadHandle)
    }

    /// Close a [`Handle`], potentially orphaning the underlying [`channel::Channel`].
    pub fn channel_close(&self, reference: Handle) -> Result<(), OakStatus> {
        self.channels.remove_reference(reference)
    }

    /// Create a fresh [`NodeRef`].
    fn new_node_reference(&self) -> NodeRef {
        NodeRef(self.next_node_reference.fetch_add(1, SeqCst))
    }
}

/// A reference to a [`Runtime`].
#[derive(Clone)]
pub struct RuntimeRef(Arc<Runtime>);

impl RuntimeRef {
    /// Thread safe method that attempts to create a node within the [`Runtime`] corresponding to a
    /// given module name and entrypoint. The `reader: ChannelReader` is passed to the newly
    /// created node.
    ///
    /// The caller also specifies a [`oak_abi::label::Label`], which is assigned to the newly
    /// created node. See <https://github.com/project-oak/oak/blob/master/docs/concepts.md#labels>
    /// for more information on labels.
    ///
    /// [`RuntimeRef::node_create`] is a method of [`RuntimeRef`] and not [`Runtime`], so that the
    /// underlying `Arc<Runtime>` can be passed to [`crate::node::Configuration::new_instance`]
    /// and given to a new node thread.
    pub fn node_create(
        &self,
        module_name: &str,
        entrypoint: &str,
        label: &oak_abi::label::Label,
        reader: Handle,
    ) -> Result<(), OakStatus> {
        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        // TODO(#630): Check whether the label of the caller "flows to" the provided label. In order
        // to do that we first need to provide a reference to the caller node as a parameter to this
        // function.

        let mut nodes = self.nodes.lock().unwrap();
        let reference = self.new_node_reference();

        let reader = self.channels.duplicate_reference(reader)?;

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
                nodes.insert(
                    reference,
                    Node {
                        reference,
                        join_handle,
                        label: label.clone(),
                    },
                );
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
