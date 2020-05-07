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

use crate::runtime::RuntimeProxy;
use log::{error, info, log};
use oak_abi::proto::oak::log::{Level, LogMessage};
use prost::Message;
use std::string::String;

/// Logging pseudo-Node.
pub struct LogNode {
    node_name: String,
}

impl LogNode {
    /// Creates a new [`LogNode`] instance, but does not start it.
    pub fn new(node_name: &str) -> Self {
        Self {
            node_name: node_name.to_string(),
        }
    }
}

impl super::Node for LogNode {
    /// Main execution loop for the logging pseudo-Node just waits for incoming
    /// `LogMessage`s and outputs them.
    fn run(self: Box<Self>, runtime: RuntimeProxy, handle: oak_abi::Handle) {
        loop {
            // An error indicates the Runtime is terminating. We ignore it here and keep trying to
            // read in case a Wasm Node wants to emit remaining messages. We will return
            // once the channel is closed.
            let _ = runtime.wait_on_channels(&[handle]);

            match runtime.channel_read(handle) {
                Ok(Some(message)) => match LogMessage::decode(&*message.data) {
                    Ok(msg) => log!(
                        target: &format!("{}:{}", msg.file, msg.line),
                        to_level(msg.level),
                        "{}",
                        msg.message,
                    ),
                    Err(error) => {
                        error!("{} Could not parse LogMessage: {}", self.node_name, error)
                    }
                },
                Ok(None) => {}
                Err(status) => {
                    error!("{} Failed channel read: {:?}", self.node_name, status);
                    break;
                }
            }
        }
        info!("{} logger execution complete", self.node_name);
        let _ = runtime.channel_close(handle);
    }
}

/// Translate a log level as encoded in a `LogMessage` into the corresponding
/// enum value from the [`log` crate](https://crates.io/crates/log).
fn to_level(level: i32) -> log::Level {
    match Level::from_i32(level).unwrap_or(Level::UnknownLevel) {
        Level::UnknownLevel => log::Level::Error,
        Level::Error => log::Level::Error,
        Level::Warn => log::Level::Warn,
        Level::Info => log::Level::Info,
        Level::Debugging => log::Level::Debug,
        Level::Trace => log::Level::Trace,
    }
}
