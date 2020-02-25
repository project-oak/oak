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

use std::collections::{HashMap, HashSet};
use std::string::String;
use std::sync::Arc;

use core::sync::atomic::{AtomicBool, AtomicUsize};
use core::sync::atomic::Ordering::SeqCst;

use log::{debug, error};

use oak_abi::{ChannelReadStatus, OakStatus};

use crate::channel;
use crate::message::Message;
use crate::channel::Channel;
use crate::node::{load_wasm, NodeConfiguration};
use crate::platform;
use crate::proto;
use crate::proto::application::NodeConfiguration_oneof_config_type;

#[derive(PartialEq, Eq, Hash)]
pub struct ChannelWriter(usize);
#[derive(PartialEq, Eq, Hash)]
pub struct ChannelReader(usize);

struct ChannelInfo {
    channel: Channel,
    readers: HashSet<ChannelReader>,
    writers: HashSet<ChannelWriter>,
}

#[derive(Clone, Copy)]
struct ChannelRef(usize);

/// A wrapper type to allow taking channel references without discriminating on direction. Used
/// when adding `ChannelRef`s into `Message`s.
// #[derive(Clone)]
pub enum ChannelEither<'a> {
    Writer(&'a ChannelWriter),
    Reader(&'a ChannelReader),
}

pub enum ChannelEitherOwned {
    Writer(ChannelWriter),
    Reader(ChannelReader),
}

/// Runtime structure for configuring and running a set of Oak node_threads.
pub struct Runtime {
    configurations: HashMap<String, NodeConfiguration>,
    terminating: AtomicBool,
    node_threads: platform::Mutex<Vec<platform::JoinHandle>>,

    channels: platform::Mutex<Vec<ChannelInfo>>,
    channel_readers: platform::Mutex<HashMap<ChannelReader, ChannelRef>>,
    channel_writers: platform::Mutex<HashMap<ChannelWriter, ChannelRef>>,
    next_reader: AtomicUsize,
    next_writer: AtomicUsize,
}

impl Runtime {
    /// Configure and run the protobuf specified `ApplicationConfiguration`. After creating a
    /// `Runtime` calling `stop` will send termination signals to node_threads and wait for them to
    /// terminate.
    pub fn configure_and_run(
        app_config: proto::application::ApplicationConfiguration,
    ) -> Result<(RuntimeRef, ChannelWriter), OakStatus> {
        let mut runtime = Runtime {
            configurations: HashMap::new(),
            terminating: AtomicBool::new(false),
            node_threads: platform::Mutex::new(Vec::new()),

            channels: platform::Mutex::new(Vec::new()),
            channel_writers: platform::Mutex::new(HashMap::new()),
            channel_readers: platform::Mutex::new(HashMap::new()),

            next_reader: AtomicUsize::new(0),
            next_writer: AtomicUsize::new(0),
        };

        for config in app_config.get_node_configs() {
            runtime.configurations.insert(
                config.name.clone(),
                match &config.config_type {
                    None => {
                        error!("Node config {} with no type", config.name);
                        return Err(OakStatus::ERR_INVALID_ARGS);
                    }
                    Some(NodeConfiguration_oneof_config_type::log_config(_)) => {
                        NodeConfiguration::LogNode
                    }
                    Some(NodeConfiguration_oneof_config_type::wasm_config(
                        proto::application::WebAssemblyConfiguration { module_bytes, .. },
                    )) => load_wasm(&module_bytes).map_err(|e| {
                        error!("Error loading Wasm module: {}", e);
                        OakStatus::ERR_INVALID_ARGS
                    })?,
                    Some(_) => {
                        error!("Pseudo-node not implemented!");
                        return Err(OakStatus::ERR_INVALID_ARGS);
                    }
                },
            );
        }

        let runtime = RuntimeRef(Arc::new(runtime));
        let (chan_writer, chan_reader) = runtime.new_channel();

        runtime.node_create(
            &app_config.initial_node_config_name,
            &app_config.initial_entrypoint_name,
            chan_reader,
        )?;

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
        let mut channels = self.channels.lock().unwrap();

        let id = ChannelRef(channels.len());

        let reader = self.next_reader.fetch_add(1, SeqCst);
        let writer = self.next_writer.fetch_add(1, SeqCst);

        channels.push(ChannelInfo{
            channel: channel::Channel::new(),
            readers: vec![ChannelReader(reader)].into_iter().collect(),
            writers: vec![ChannelWriter(writer)].into_iter().collect(),
        });

        let mut readers = self.channel_readers.lock().unwrap();
        readers.insert(ChannelReader(reader), id);

        let mut writers = self.channel_writers.lock().unwrap();
        writers.insert(ChannelWriter(writer), id);

        (ChannelWriter(writer), ChannelReader(reader))
    }

    pub fn is_orphan<'a>(&self, ref_: ChannelEither<'a>) -> bool {
        let channel_id = match ref_ {
            ChannelEither::Reader(reader) => {
                let channel_readers = self.channel_readers.lock().unwrap();
                channel_readers.get(reader).map(|x|x.0)
            }
            ChannelEither::Writer(writer) => {
                let channel_writers = self.channel_writers.lock().unwrap();
                channel_writers.get(writer).map(|x|x.0)
            }
        };

        match channel_id {
            None => true,
            Some(channel_id) => {
                let channels = self.channels.lock().unwrap();
                channels[channel_id].writers.len() == 0 ||
                channels[channel_id].readers.len() == 0
            }
        }
    }

    pub fn close_channel<'a>(&self, ref_: ChannelEither<'a>) {
        let channel_id = match ref_ {
            ChannelEither::Reader(reader) => {
                let mut channel_readers = self.channel_readers.lock().unwrap();
                channel_readers.remove(reader).map(|x|x.0)
            }
            ChannelEither::Writer(writer) => {
                let mut channel_writers = self.channel_writers.lock().unwrap();
                channel_writers.remove(writer).map(|x|x.0)
            }
        };

        match channel_id {
            None => (),
            Some(channel_id) => {
                let mut channels = self.channels.lock().unwrap();

                match ref_ {
                    ChannelEither::Reader(reader) =>
                        channels[channel_id].readers.remove(reader),
                    ChannelEither::Writer(writer) =>
                        channels[channel_id].writers.remove(writer),
                };
            }
        }
    }

    pub fn write_channel(&self, writer: &ChannelWriter, msg: Message) -> Result<(), OakStatus> {
        let chan = {
            let channel_writers = self.channel_writers.lock().unwrap();
            match channel_writers.get(writer) {
                None => return Err(OakStatus::ERR_BAD_HANDLE),
                Some(x) => x.0
            }
        };

        if self.is_orphan(ChannelEither::Writer(writer)) {
            return Err(OakStatus::ERR_CHANNEL_CLOSED);
        }

        let channels = self.channels.lock().unwrap();
        Ok(channels[chan].channel.write(msg))
    }

    pub fn read_channel(&self, reader: &ChannelReader) -> Result<Option<Message>, OakStatus> {
        let chan = {
            let channel_readers = self.channel_readers.lock().unwrap();
            match channel_readers.get(reader) {
                None => return Err(OakStatus::ERR_BAD_HANDLE),
                Some(x) => x.0
            }
        };
        let is_orphan = self.is_orphan(ChannelEither::Reader(reader));
        let channels = self.channels.lock().unwrap();

        match channels[chan].channel.read() {
            None => {
                if is_orphan {
                    Err(OakStatus::ERR_CHANNEL_CLOSED)
                } else {
                    Ok(None)
                }
            }
            Some(m) => Ok(Some(m)),
        }
    }

    pub fn channel_status(&self, reader: &ChannelReader) -> ChannelReadStatus {
        let chan = {
            let channel_readers = self.channel_readers.lock().unwrap();
            match channel_readers.get(reader) {
                None => return ChannelReadStatus::ORPHANED,
                Some(x) => x.0
            }
        };
        let is_orphan = self.is_orphan(ChannelEither::Reader(reader));
        let channels = self.channels.lock().unwrap();

        if channels[chan].channel.status() {
            ChannelReadStatus::READ_READY
        } else if is_orphan {
            ChannelReadStatus::ORPHANED
        } else {
            ChannelReadStatus::NOT_READY
        }
    }

    pub fn channel_try_read(&self, reader: &ChannelReader,
        bytes_capacity: usize,
        handles_capacity: usize,
    ) -> Result<Option<channel::ReadStatus>, OakStatus> {

        let chan = {
            let channel_readers = self.channel_readers.lock().unwrap();
            match channel_readers.get(reader) {
                None => return Err(OakStatus::ERR_CHANNEL_CLOSED),
                Some(x) => x.0
            }
        };
        let is_orphan = self.is_orphan(ChannelEither::Reader(reader));
        let channels = self.channels.lock().unwrap();

        channels[chan].channel.try_read_message(bytes_capacity,handles_capacity,is_orphan)
    }

    pub fn channel_read(&self, reader: &ChannelReader
    ) -> Result<Option<Message>, OakStatus> {
        let chan = {
            let channel_readers = self.channel_readers.lock().unwrap();
            match channel_readers.get(reader) {
                None => return Err(OakStatus::ERR_CHANNEL_CLOSED),
                Some(x) => x.0
            }
        };
        let is_orphan = self.is_orphan(ChannelEither::Reader(reader));
        let channels = self.channels.lock().unwrap();

        match channels[chan].channel.read() {
            Some(m) => Ok(Some(m)),
            None =>
             if is_orphan {
                Err(OakStatus::ERR_CHANNEL_CLOSED)
            } else {
                Ok(None)
            }
        }
    }

    pub fn channel_add_waiter(&self, reader: &ChannelReader,
        thread: &Arc<platform::thread::Thread>,
    ) {
        let chan = {
            let channel_readers = self.channel_readers.lock().unwrap();
            channel_readers.get(reader).map(|x|x.0)
        }.expect("no such channel");
        let channels = self.channels.lock().unwrap();

        channels[chan].channel.add_waiter(thread);
    }

    pub fn readers_statuses(&self,
        readers: &[Option<&ChannelReader>]
    ) -> Vec<ChannelReadStatus> {
        readers
            .iter()
            .map(|chan| chan.map_or(ChannelReadStatus::INVALID_CHANNEL, |chan| self.channel_status(chan)))
            .collect()
    }

    pub fn clone_reader(&self, reader: &ChannelReader) -> ChannelReader {
        let chan = {
            let channel_readers = self.channel_readers.lock().unwrap();
            channel_readers.get(reader).map(|x|x.0)
        }.expect("no such channel");

        let new_reader = self.next_reader.fetch_add(1, SeqCst);

        let mut channels = self.channels.lock().unwrap();
        channels[chan].readers.insert(ChannelReader(new_reader));

        let mut readers = self.channel_readers.lock().unwrap();
        readers.insert(ChannelReader(new_reader), ChannelRef(chan));

        ChannelReader(new_reader)
    }

    pub fn clone_writer(&self, writer: &ChannelWriter) -> ChannelWriter {
        let chan = {
            let channel_writers = self.channel_writers.lock().unwrap();
            channel_writers.get(writer).map(|x|x.0)
        }.expect("no such channel");

        let new_writer = self.next_writer.fetch_add(1, SeqCst);

        let mut channels = self.channels.lock().unwrap();
        channels[chan].writers.insert(ChannelWriter(new_writer));

        let mut writers = self.channel_writers.lock().unwrap();
        writers.insert(ChannelWriter(new_writer), ChannelRef(chan));

        ChannelWriter(new_writer)
    }

    pub fn clone_either(&self, ref_: &ChannelEitherOwned) -> ChannelEitherOwned {
        match ref_ {
            ChannelEitherOwned::Reader(r) => ChannelEitherOwned::Reader(self.clone_reader(r)),
            ChannelEitherOwned::Writer(r) => ChannelEitherOwned::Writer(self.clone_writer(r)),
        }
    }

    pub fn wait_on_channels(
        &self,
        readers: &[Option<&ChannelReader>],
    ) -> Result<Vec<ChannelReadStatus>, OakStatus> {
        let thread = platform::thread::current();
        while !self.is_terminating() {
            let thread_ref = Arc::new(thread.clone());

            for reader in readers {
                if let Some(reader) = reader {
                    self.channel_add_waiter(reader, &thread_ref);
                }
            }
            let statuses = self.readers_statuses(readers);

            let all_unreadable = statuses
                .iter()
                .all(|&s| s == ChannelReadStatus::INVALID_CHANNEL || s == ChannelReadStatus::ORPHANED);
            let any_ready = statuses.iter().any(|&s| s == ChannelReadStatus::READ_READY);

            if all_unreadable || any_ready {
                return Ok(statuses);
            }

            debug!(
                "wait_on_channels: channels not ready, parking thread {:?}",
                platform::thread::current()
            );

            platform::thread::park();

            debug!(
                "wait_on_channels: thread {:?} re-woken",
                platform::thread::current()
            );
        }
        Err(OakStatus::ERR_TERMINATED)
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
            return Err(OakStatus::ERR_TERMINATED);
        }

        let mut node_threads = self.node_threads.lock().unwrap();

        if self.is_terminating() {
            return Err(OakStatus::ERR_TERMINATED);
        }

        let join_handle = self
            .configurations
            .get(module_name)
            .ok_or(OakStatus::ERR_INVALID_ARGS)
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
