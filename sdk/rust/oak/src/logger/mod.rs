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

// TODO(#544)

use log::{Level, Log, Metadata, Record, SetLoggerError};

struct OakChannelLogger {
    channel: crate::io::Sender<crate::proto::log::LogMessage>,
}

impl Log for OakChannelLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }
    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        let log_msg = crate::proto::log::LogMessage {
            file: record.file().unwrap_or("<unknown-file>").to_string(),
            line: record.line().unwrap_or_default(),
            level: map_level(record.level()),
            message: format!("{}", record.args()),
            ..Default::default()
        };
        match self.channel.send(&log_msg) {
            Ok(()) => (),
            Err(crate::OakError::OakStatus(crate::OakStatus::ErrTerminated)) => (),
            Err(e) => panic!("could not send log message over log channel: {}", e),
        }
    }
    fn flush(&self) {}
}

fn map_level(level: Level) -> crate::proto::log::Level {
    match level {
        Level::Error => crate::proto::log::Level::ERROR,
        Level::Warn => crate::proto::log::Level::WARN,
        Level::Info => crate::proto::log::Level::INFO,
        Level::Debug => crate::proto::log::Level::DEBUG,
        Level::Trace => crate::proto::log::Level::TRACE,
    }
}

/// Default name for predefined Node configuration that corresponds to a logging
/// pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "log";

/// Initialize Node-wide default logging.
///
/// Uses the default level (`Debug`) and the default pre-defined name
/// (`"log"`) identifying logging Node configuration.
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
    let (write_handle, read_handle) = crate::channel_create().expect("could not create channel");
    crate::node_create(config, "oak_main", read_handle).expect("could not create node");
    crate::channel_close(read_handle.handle).expect("could not close channel");

    log::set_boxed_logger(Box::new(OakChannelLogger {
        channel: crate::io::Sender::new(write_handle),
    }))?;
    log::set_max_level(level.to_level_filter());
    Ok(())
}
