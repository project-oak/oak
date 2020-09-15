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

//! Logging pseudo-Node functionality.

use crate::RuntimeProxy;
use log::{error, info};
use oak_abi::OakStatus;
use oak_services::proto::oak::log::{Level, LogMessage};
use prost::Message;
use std::string::String;
use tokio::sync::oneshot;

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
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        'wait: loop {
            let result = runtime.wait_on_channels(&[handle]);

            // Read all available log messages (even if the Runtime is terminating).
            'read: loop {
                match runtime.channel_read(handle) {
                    Ok(Some(message)) => match LogMessage::decode(&*message.bytes) {
                        Ok(msg) => {
                            // Log messages that arrive from Oak applications over a logging channel
                            // are controlled by IFC, and so need to be emitted independently of
                            // whether the Runtime has been built with the `oak_debug` feature
                            // enabled (and thus whether log! is connected up to anything or not).
                            // So send to stderr.
                            let now: chrono::DateTime<chrono::Utc> = chrono::Utc::now();
                            let timestamp = now.to_rfc3339_opts(chrono::SecondsFormat::Secs, true);
                            eprintln!(
                                "{{{} {} {}:{}}} {}",
                                timestamp,
                                level_to_string(msg.level),
                                msg.file,
                                msg.line,
                                msg.message
                            );
                        }
                        Err(error) => {
                            error!("{} Could not parse LogMessage: {}", self.node_name, error)
                        }
                    },
                    Ok(None) => {
                        // No more log messages to read, go back to waiting.
                        break 'read;
                    }
                    Err(OakStatus::ErrChannelClosed) => {
                        info!("{} channel closed by remote", self.node_name);
                        break 'wait;
                    }
                    Err(status) => {
                        error!("{} Failed channel read: {:?}", self.node_name, status);
                        break 'wait;
                    }
                }
            }

            if result == Err(OakStatus::ErrTerminated) {
                break 'wait;
            }
        }
        info!("{} logger execution complete", self.node_name);
        let _ = runtime.channel_close(handle);
    }
}

/// Translate a log level as encoded in a `LogMessage` into a string
fn level_to_string(level: i32) -> &'static str {
    // Pad all the strings to 5 characters to try to line things up.
    match Level::from_i32(level).unwrap_or(Level::UnknownLevel) {
        Level::UnknownLevel => " N/A ",
        Level::Error => "ERROR",
        Level::Warn => "WARN ",
        Level::Info => "INFO ",
        Level::Debugging => "DEBUG",
        Level::Trace => "TRACE",
    }
}
