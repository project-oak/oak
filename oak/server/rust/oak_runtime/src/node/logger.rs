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

use std::string::String;

use log::{error, info};

use oak_abi::OakStatus;
use std::{
    thread,
    thread::{spawn, JoinHandle},
};

use crate::proto::log::{Level, LogMessage};
use crate::runtime::Handle;
use crate::{NodeId, RuntimeRef};
use prost::Message;

pub struct LogNode {
    config_name: String,
    runtime: RuntimeRef,
    node_id: NodeId,
    reader: Handle,
    thread_handle: Option<JoinHandle<()>>,
}

impl LogNode {
    /// Creates a new [`LogNode`] instance, but does not start it.
    pub fn new(config_name: &str, runtime: RuntimeRef, node_id: NodeId, reader: Handle) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            node_id,
            reader,
            thread_handle: None,
        }
    }
}

impl super::Node for LogNode {
    fn start(&mut self) -> Result<(), OakStatus> {
        // Clone or copy all the captured values and move them into the closure, for simplicity.
        let config_name = self.config_name.clone();
        let runtime = self.runtime.clone();
        let node_id = self.node_id;
        let reader = self.reader;
        // TODO(#770): Use `std::thread::Builder` and give a name to this thread.
        let thread_handle = spawn(move || {
            let pretty_name = format!("{}-{:?}:", config_name, thread::current());
            let result = logger(&pretty_name, runtime.clone(), node_id, reader);
            info!("{} LOG: exiting log thread {:?}", pretty_name, result);
            runtime.remove_node_id(node_id);
        });
        self.thread_handle = Some(thread_handle);
        Ok(())
    }
    fn stop(&mut self) {
        if let Some(join_handle) = self.thread_handle.take() {
            if let Err(err) = join_handle.join() {
                error!("error while stopping log node: {:?}", err);
            }
        }
    }
}

fn logger(
    pretty_name: &str,
    runtime: RuntimeRef,
    node_id: NodeId,
    reader: Handle,
) -> Result<(), OakStatus> {
    loop {
        // An error indicates the runtime is terminating. We ignore it here and keep trying to read
        // in case a Wasm node wants to emit remaining messages. We will return once the channel is
        // closed.

        // TODO(#646): Temporarily don't wait for messages when terminating. Renable when channels
        // track their channels and make sure all channels are closed.
        // let _ = runtime.wait_on_channels(&[Some(&reader)]);
        runtime.wait_on_channels(node_id, &[Some(reader)])?;

        if let Some(message) = runtime.channel_read(node_id, reader)? {
            match LogMessage::decode(&*message.data) {
                Ok(msg) => info!(
                    "{} LOG: {} {}:{}: {}",
                    pretty_name,
                    to_level_name(msg.level),
                    msg.file,
                    msg.line,
                    msg.message
                ),
                Err(error) => error!("{} Could not parse LogMessage: {}", pretty_name, error),
            }
        }
    }
}

fn to_level_name(level: i32) -> String {
    format!(
        "{:?}",
        Level::from_i32(level).unwrap_or(Level::UnknownLevel)
    )
    .to_ascii_uppercase()
}
