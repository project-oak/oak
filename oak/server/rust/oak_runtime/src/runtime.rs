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

use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering::SeqCst;

use oak_abi::{ChannelReadStatus, OakStatus};
use oak_platform::{JoinHandle, Mutex};

use log::debug;

use crate::node;

mod channel;
pub use channel::{ChannelEither, ChannelWriter, ChannelReader, ReadStatus};

type Channels = Vec<Weak<channel::Channel>>;

pub struct Configuration {
    pub nodes:        HashMap<String, node::Configuration>,
    pub entry_module: String,
    pub entrypoint:   String,
}

/// Runtime structure for configuring and running a set of Oak nodes.
pub struct Runtime {
    configurations: HashMap<String, node::Configuration>,
    terminating:    AtomicBool,
    channels:       Mutex<Channels>,
    // nodes:          Nodes,
    node_threads:   Mutex<Vec<JoinHandle>>,
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
            node_threads: Mutex::new(Vec::new()),
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
        let handles = {
            let mut node_threads = self.node_threads.lock().unwrap();
            self.terminating.store(true, SeqCst);

            std::mem::replace(&mut *node_threads, vec![])
        };

        // Unpark any threads that are blocked waiting on channels.
        for handle in handles.iter() {
            handle.thread().unpark();
        }

        for handle in handles {
            handle.join().expect("Failed to join handle");
        }
    }

    pub fn new_channel(&self) -> (ChannelWriter, ChannelReader) {
        // TODO: channel::new could take id or pretty name here
        let (c,w,r) = channel::new();
        let mut channels = self.channels.lock().unwrap();
        channels.push(Arc::downgrade(&c));
        (w,r)
    }

    /// Reads the statuses from a slice of `Option<&ChannelReader>`s.
    /// `ChannelReadStatus::InvalidChannel` is set for `None` readers in the slice. For `Some(_)`
    /// readers, the result is set from a call to `has_message`.
    fn readers_statuses(readers: &[Option<&ChannelReader>]) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|chan| chan.map_or(ChannelReadStatus::InvalidChannel, |chan| chan.status()))
            .collect()
    }

    /// Waits on a slice of `Option<&ChannelReader>`s, blocking until one of the following conditions:
    /// - If the `Runtime` is terminating this will return immediately with an `ErrTerminated` status
    ///   for each channel.
    /// - If all readers are in an erroneous status, e.g. when all `ChannelReaders` are orphaned, this
    ///   will immediately return the channels statuses.
    /// - If any of the channels is able to read a message, the corresponding element in the returned
    ///   vector will be set to `Ok(ReadReady)`, with `Ok(NotReady)` signaling the channel has no
    ///   message available
    ///
    /// In particular, if there is at least one channel in good status and no messages on said channel
    /// available, `wait_on_channels` will continue to block until a message is available.
    pub fn wait_on_channels(
        &self,
        readers: &[Option<&ChannelReader>],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        let thread = oak_platform::current_thread();
        while !self.is_terminating() {
            // Create a new Arc each iteration to be dropped after `thread::park` e.g. when the thread
            // is resumed. When the Arc is deallocated, any remaining `Weak` references in
            // `Channel`s will be orphaned. This means thread::unpark will not be called multiple times.
            // Even if thread unpark is called spuriously and we wake up early, no channel
            // statuses will be ready and so we can just continue.
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
            let statuses = Runtime::readers_statuses(readers);

            let all_unreadable = statuses
                .iter()
                .all(|&s| s == ChannelReadStatus::InvalidChannel || s == ChannelReadStatus::Orphaned);
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

        let mut node_threads = self.node_threads.lock().unwrap();

        if self.is_terminating() {
            return Err(OakStatus::ErrTerminated);
        }

        let join_handle = self
            .configurations
            .get(module_name)
            .ok_or(OakStatus::ErrInvalidArgs)
            .and_then(|conf| {
                conf.new_instance(module_name, self.clone(), entrypoint.to_owned(), reader)
            })?;
        node_threads.push(join_handle);

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
