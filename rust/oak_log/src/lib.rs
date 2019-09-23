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

extern crate log;
extern crate oak;

#[cfg(test)]
mod tests;

use log::{Level, Log, Metadata, Record, SetLoggerError};
use std::io::Write;

struct OakChannelLogger {
    channel_handle: oak::Handle,
}

impl Log for OakChannelLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }
    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        // Only flush logging channel on newlines.
        let mut channel = std::io::LineWriter::new(oak::SendChannelHalf::new(self.channel_handle));
        writeln!(
            &mut channel,
            "{}  {} : {} : {}",
            record.level(),
            record.file().unwrap_or_default(),
            record.line().unwrap_or_default(),
            record.args()
        )
        .unwrap();
    }
    fn flush(&self) {}
}

/// Initialize Node-wide default logging.
///
/// Uses the default level (`Debug`) and the default pre-defined port name
/// (`"log"`) for the logging channel from the current Node.
///
/// # Panics
///
/// Panics if a logger has already been set.
pub fn init_default() {
    init(Level::Debug, oak::channel_find("log")).unwrap();
}

/// Initialize Node-wide logging via a channel.
///
/// Initialize logging at the given level, using the send channel half
/// identified by the given port name.
///
/// # Errors
///
/// An error is returned if a logger has already been set.
pub fn init(level: Level, channel_handle: oak::Handle) -> Result<(), SetLoggerError> {
    log::set_boxed_logger(Box::new(OakChannelLogger { channel_handle }))?;
    log::set_max_level(level.to_level_filter());
    Ok(())
}
