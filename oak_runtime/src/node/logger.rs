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

use crate::{
    io::{Receiver, ReceiverExt},
    RuntimeProxy,
};
use log::{error, info, warn};
use oak_abi::OakStatus;
use oak_io::{handle::ReadHandle, OakError};
use oak_services::proto::oak::log::{Level, LogMessage};
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
    fn node_type(&self) -> &'static str {
        "logger"
    }

    /// Main execution loop for the logging pseudo-Node just waits for incoming
    /// `LogMessage`s and outputs them.
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        let receiver = Receiver::<LogMessage>::new(ReadHandle { handle });
        loop {
            match receiver.receive(&runtime) {
                Ok(msg) => {
                    // Log messages that arrive from Oak applications over a logging channel
                    // are controlled by IFC, and so need to be emitted independently of
                    // whether the Runtime has been built with the `oak-unsafe` feature
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
                // Recoverable errors:
                Err(OakError::ProtobufDecodeError(err)) => {
                    warn!("{} failed to decode log message: {:?}", self.node_name, err);
                }
                // Errors that lead to Node termination:
                Err(OakError::OakStatus(OakStatus::ErrTerminated)) => break,
                Err(OakError::OakStatus(OakStatus::ErrChannelClosed)) => {
                    info!("{} channel closed", self.node_name);
                    break;
                }
                Err(err) => {
                    error!("{} failed channel receive: {:?}", self.node_name, err);
                    break;
                }
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
