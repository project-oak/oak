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

use crate::io::{Sender, SenderExt};
use log::{Level, Log, Metadata, Record, SetLoggerError};
use oak_abi::{
    label::{confidentiality_label, top, Label},
    OakStatus,
};
use oak_services::proto::oak::log::LogMessage;

struct OakChannelLogger {
    log_sender: Sender<LogMessage>,
}

impl Log for OakChannelLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }
    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        let log_msg = oak_services::proto::oak::log::LogMessage {
            file: record.file().unwrap_or("<unknown-file>").to_string(),
            line: record.line().unwrap_or_default(),
            level: map_level(record.level()) as i32,
            message: format!("{}", record.args()),
        };
        match self.log_sender.send(&log_msg) {
            Ok(()) => (),
            Err(crate::OakError::OakStatus(crate::OakStatus::ErrTerminated)) => (),
            // If the current node does not have permissions to log we should not panic. It is
            // expected that nodes could try to log even when IFC would block the message, and this
            // should not terminate the node.
            Err(crate::OakError::OakStatus(crate::OakStatus::ErrPermissionDenied)) => (),
            Err(e) => panic!("could not send log message over log channel: {}", e),
        }
    }
    fn flush(&self) {}
}

fn map_level(level: Level) -> oak_services::proto::oak::log::Level {
    match level {
        Level::Error => oak_services::proto::oak::log::Level::Error,
        Level::Warn => oak_services::proto::oak::log::Level::Warn,
        Level::Info => oak_services::proto::oak::log::Level::Info,
        Level::Debug => oak_services::proto::oak::log::Level::Debugging,
        Level::Trace => oak_services::proto::oak::log::Level::Trace,
    }
}

/// Initialize Node-wide logging via a channel to a logging pseudo-Node.
///
/// Initialize logging at the given level, creating a logging pseudo-Node
/// whose configuration is identified by the given name.
///
/// # Errors
///
/// An error is returned if a logger has already been set.
pub fn init(log_sender: Sender<LogMessage>, level: Level) -> Result<(), SetLoggerError> {
    log::set_boxed_logger(Box::new(OakChannelLogger { log_sender }))?;
    log::set_max_level(level.to_level_filter());
    Ok(())
}

pub fn create() -> Result<Sender<LogMessage>, OakStatus> {
    // If we get a permission-denied error when creating the logger Node with top secret
    // confidentiality it means that the Runtime was not built with the `oak-unsafe` feature, so
    // we try to create it as a public Node.
    for label in &[confidentiality_label(top()), Label::public_untrusted()] {
        match crate::io::node_create("log", label, &crate::node_config::log()) {
            Ok(log_node) => return Ok(log_node),
            Err(crate::OakStatus::ErrPermissionDenied) => continue,
            Err(e) => return Err(e),
        }
    }
    Err(crate::OakStatus::ErrPermissionDenied)
}
