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

use std::{
    fmt::{self, Display, Formatter},
    string::String,
};

use log::{error, info};

use oak_abi::OakStatus;
use std::thread::{self, JoinHandle};

use crate::{
    pretty_name_for_thread,
    runtime::{Handle, RuntimeProxy},
};
use oak_abi::proto::oak::log::{Level, LogMessage};
use prost::Message;

pub struct LogNode {
    config_name: String,
    runtime: RuntimeProxy,
    reader: Handle,
}

impl LogNode {
    /// Creates a new [`LogNode`] instance, but does not start it.
    pub fn new(config_name: &str, runtime: RuntimeProxy, reader: Handle) -> Self {
        Self {
            config_name: config_name.to_string(),
            runtime,
            reader,
        }
    }

    /// Main node worker thread.
    fn worker_thread(self) {
        let pretty_name = pretty_name_for_thread(&thread::current());
        let result = self.logger_loop(&pretty_name);
        info!("{} LOG: exiting log thread {:?}", pretty_name, result);
        self.runtime.exit_node();
    }

    fn logger_loop(&self, pretty_name: &str) -> Result<(), OakStatus> {
        loop {
            // An error indicates the Runtime is terminating. We ignore it here and keep trying to
            // read in case a Wasm Node wants to emit remaining messages. We will return
            // once the channel is closed.

            let _ = self.runtime.wait_on_channels(&[Some(self.reader)]);

            if let Some(message) = self.runtime.channel_read(self.reader)? {
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
}

impl Display for LogNode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "LogNode({})", self.config_name)
    }
}

impl super::Node for LogNode {
    fn start(self: Box<Self>) -> Result<JoinHandle<()>, OakStatus> {
        let thread_handle = thread::Builder::new()
            .name(self.to_string())
            .spawn(move || self.worker_thread())
            .expect("failed to spawn thread");
        Ok(thread_handle)
    }
}

fn to_level_name(level: i32) -> String {
    format!(
        "{:?}",
        Level::from_i32(level).unwrap_or(Level::UnknownLevel)
    )
    .to_ascii_uppercase()
}
