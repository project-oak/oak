//
// Copyright 2019 The Project Oak Authors
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

//! A logger that sends output to an Oak logging channel, for use with
//! the [log facade].
//!
//! [log facade]: https://crates.io/crates/log

#[cfg(test)]
mod tests;

use log::{Level, Log, Metadata, Record, SetLoggerError};

struct OakChannelLogger {
    channel: oak::io::Sender<LogEntry>,
}

/// An object representing a log entry. Currently just a wrapper around a string, but it may be
/// extended in the future with additional fields, e.g. level or file / line information, though
/// that would probably require defining a cross-language schema such as protobuf or FIDL for it,
/// rather than just a Rust struct.
struct LogEntry {
    message: String,
}

/// Trivial implementation of [`oak::io::Encodable`], just converting the log entry message to bytes
/// and no handles.
impl oak::io::Encodable for LogEntry {
    fn encode(&self) -> Result<oak::io::Message, oak::OakError> {
        let bytes = self.message.as_bytes().into();
        let handles = vec![];
        Ok(oak::io::Message { bytes, handles })
    }
}

impl Log for OakChannelLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }
    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        let log_entry = LogEntry {
            // We add a newline to the message to force flushing when printed by the host.
            message: format!(
                "{}  {} : {} : {}\n",
                record.level(),
                record.file().unwrap_or_default(),
                record.line().unwrap_or_default(),
                record.args()
            ),
        };
        self.channel
            .send(&log_entry)
            .expect("could not send log message over log channel");
    }
    fn flush(&self) {}
}

/// Default name for predefined node configuration that corresponds to a logging
/// pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "log";

/// Initialize Node-wide default logging.
///
/// Uses the default level (`Debug`) and the default pre-defined name
/// (`"log"`) identifying logging node configuration.
///
/// # Panics
///
/// Panics if a logger has already been set.
pub fn init_default() {
    init(Level::Debug, DEFAULT_CONFIG_NAME).unwrap();
}

/// Initialize Node-wide logging via a channel to a logging pseudo-Node.
///
/// Initialize logging at the given level, creating a logging pseudo-Node
/// whose configuration is identified by the given name.
///
/// # Errors
///
/// An error is returned if a logger has already been set.
pub fn init(level: Level, config: &str) -> Result<(), SetLoggerError> {
    // Create a channel and pass the read half to a fresh logging Node.
    let (write_handle, read_handle) = oak::channel_create().expect("could not create channel");
    oak::node_create(config, read_handle).expect("could not create node");
    oak::channel_close(read_handle.handle).expect("could not close channel");

    log::set_boxed_logger(Box::new(OakChannelLogger {
        channel: oak::io::Sender::new(write_handle),
    }))?;
    log::set_max_level(level.to_level_filter());
    Ok(())
}
