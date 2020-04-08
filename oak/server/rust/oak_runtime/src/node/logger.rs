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

use std::fmt::{self, Display, Formatter};
use std::string::String;

use log::{error, info};

use oak_abi::OakStatus;
use std::thread::{self, JoinHandle};

use crate::pretty_name_for_thread;
use crate::proto::log::{Level, LogMessage};
use crate::runtime::ChannelHalfId;
use crate::runtime::RuntimeProxy;
use prost::Message;

pub struct LogNode {
    config_name: String,
    runtime: RuntimeProxy,
    reader: ChannelHalfId,
    thread_handle: Option<JoinHandle<()>>,
}

impl LogNode {
    /// Creates a new [`LogNode`] instance, but does not start it.
    pub fn new(config_name: &str, runtime: RuntimeProxy, reader: ChannelHalfId) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            reader,
            thread_handle: None,
        }
    }
}

impl Display for LogNode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "LogNode({})", self.config_name)
    }
}

impl super::Node for LogNode {
    fn start(&mut self) -> Result<(), OakStatus> {
        // Clone or copy all the captured values and move them into the closure, for simplicity.
        let runtime = self.runtime.clone();
        let reader = self.reader;
        let thread_handle = thread::Builder::new()
            .name(self.to_string())
            .spawn(move || {
                let pretty_name = pretty_name_for_thread(&thread::current());
                let result = logger(&pretty_name, &runtime, reader);
                info!("{} LOG: exiting log thread {:?}", pretty_name, result);
                runtime.exit_node();
            })
            .expect("failed to spawn thread");
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
    runtime: &RuntimeProxy,
    reader: ChannelHalfId,
) -> Result<(), OakStatus> {
    loop {
        // An error indicates the runtime is terminating. We ignore it here and keep trying to read
        // in case a Wasm node wants to emit remaining messages. We will return once the channel is
        // closed.

        let _ = runtime.wait_on_channels(&[Some(reader)]);

        if let Some(message) = runtime.channel_read(reader)? {
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
